#ifndef K3_RUNTIME_ENDPOINT_H
#define K3_RUNTIME_ENDPOINT_H

#include <list>
#include <map>
#include <memory>
#include <tuple>
#include <boost/thread/externally_locked.hpp>
#include <boost/thread/lockable_adapter.hpp>
#include <boost/thread/shared_lock_guard.hpp>
#include <boost/thread/shared_mutex.hpp>
#include <runtime/cpp/Common.hpp>
#include <runtime/cpp/Network.hpp>
#include <runtime/cpp/IOHandle.hpp>
#include <runtime/cpp/Queue.hpp>

// TODO: rewrite endpoint and connection containers without externally_locked as this requires a strict_lock.
// Ideally we want to use a shared_lock since the most common operation will be read accesses.

namespace K3
{
  using namespace std;

  using boost::mutex;
  using boost::strict_lock;
  using boost::shared_mutex;
  using boost::shared_lockable_adapter;
  using boost::shared_lock_guard;
  using boost::externally_locked;
  using boost::basic_lockable_adapter;

  typedef tuple<int, int> BufferSpec;

  enum class EndpointNotification { NullEvent, FileData, FileClose, SocketAccept, SocketData, SocketClose };

  class Endpoint;
  typedef map<Identifier, shared_ptr<Endpoint> > EndpointMap;

  int bufferMaxSize(BufferSpec& spec)   { return get<0>(spec); }
  int bufferBatchSize(BufferSpec& spec) { return get<1>(spec); }

  string internalEndpointPrefix() { return string("__");  }
  
  Identifier connectionId(Address& addr) {
    return internalEndpointPrefix() + "_conn_" + addressAsString(addr);
  }

  Identifier peerEndpointId(Address& addr) {
    return internalEndpointPrefix() + "_node_" + addressAsString(addr);
  }

  bool externalEndpointId(Identifier& id) {
    string pfx = internalEndpointPrefix();
    return ( mismatch(pfx.begin(), pfx.end(), id.begin()).first != pfx.end() );
  }


  //------------------------
  // Endpoint buffers.
  // In contrast to the Haskell engine, in C++ we implement the concept of the
  // BufferContents datatype inline in the EndpointBuffer class. This is due
  // to the difference in the concurrency abstractions (e.g., MVar vs. externally_locked).

  class EndpointBuffer {
  public:

    EndpointBuffer() {}

    virtual bool empty() = 0;
    virtual bool full() = 0;
    virtual size_t size() = 0;
    virtual size_t capacity() = 0;

    // Appends to this buffer, returning the value if the append fails.
    virtual shared_ptr<Value> append(shared_ptr<Value> v) = 0;

    // Transfers from this buffer into the given queues.
    virtual void enqueue(shared_ptr<MessageQueues> queues) = 0;

    // TODO
    // Writes the content of this buffer to the given IO handle. 
    // Returns a notification if the write is successfully performed.
    virtual EndpointNotification flush(shared_ptr<IOHandle> ioh) = 0;
    
    // Refresh this buffer by reading a value from the IO handle.
    // If the buffer is full, a value is returned. Also, a notification
    // is returned if the read is successfully performed.
    virtual tuple<shared_ptr<Value>, EndpointNotification>
    refresh(shared_ptr<IOHandle> ioh) = 0;
  };

  class ScalarEPBufferST : public EndpointBuffer
  {
  public:
    typedef Value BufferContents;

    ScalarEPBufferST() {}

    bool empty() { return !contents; }
    bool full() { return static_cast<bool>(contents); }
    size_t size() { return contents? 1 : 0; }
    size_t capacity () { return 1; }

    shared_ptr<Value> append(shared_ptr<Value> v) {
      shared_ptr<Value> r;
      if ( !contents ) { contents = v; }
      else { r = v; }
      return r;
    }

    // TODO: Value vs Message
    void enqueue(shared_ptr<MessageQueues> queues) {
      if ( contents ) { 
        queues->enqueue(*contents);
        contents.reset();
      }
    }

    EndpointNotification flush(shared_ptr<IOHandle> ioh)
    {
      EndpointNotification nt = EndpointNotification::NullEvent;
      if ( contents ) {
        ioh->doWrite(*contents);
        nt = (ioh->builtin() || ioh->file())?
                EndpointNotification::FileData : EndpointNotification::SocketData;
      }
      return nt;
    }

    tuple<shared_ptr<Value>, EndpointNotification>
    refresh(shared_ptr<IOHandle> ioh)
    {
      EndpointNotification nt = EndpointNotification::NullEvent;
      shared_ptr<Value> r;

      // Read from the buffer (if possible)
      if ( contents ) { r = contents;  }
      
      // If there is more data in the underlying IOHandle
      // use it to populate the buffer
      if ( ioh->hasRead() ) {
        shared_ptr<Value> v = ioh->doRead();
        contents = v;
        nt = (ioh->builtin() || ioh->file())?
                EndpointNotification::FileData : EndpointNotification::SocketData;
      }
      else {
        // Empty the buffer
        contents = shared_ptr<BufferContents>();
      }      
      // Return the value extracted from the buffer, along with EPNotification
      return make_tuple(r, nt);
    }

  protected:
    shared_ptr<BufferContents> contents;
  };


  class ScalarEPBufferMT : public EndpointBuffer, public basic_lockable_adapter<mutex>
  {
  public:
    typedef ScalarEPBufferMT LockB;
    typedef Value BufferContents;

    ScalarEPBufferMT() : contents(*this) {}

    bool empty() { strict_lock<LockB> guard(*this); return !(contents.get(guard)); }
    bool full() { strict_lock<LockB> guard(*this); return static_cast<bool>(contents.get(guard)); }
    size_t size() { strict_lock<LockB> guard(*this); return contents.get(guard)? 1 : 0; }
    size_t capacity () { return 1; }


    shared_ptr<Value> append(shared_ptr<Value> v)
    {
      strict_lock<LockB> guard(*this);
      shared_ptr<Value> r;
      if ( !contents.get(guard) ) { contents.get(guard) = v; }
      else { r = v; }
      return r;
    }

    // TODO: Value vs Message
    void enqueue(shared_ptr<MessageQueues> queues)
    {
      strict_lock<LockB> guard(*this);
      if ( shared_ptr<Value> r = contents.get(guard) ) { 
        queues->enqueue(*r);
        contents.get(guard).reset();
      }
    }

    EndpointNotification flush(shared_ptr<IOHandle> ioh)
    {
      strict_lock<LockB> guard(*this);
      EndpointNotification nt = EndpointNotification::NullEvent;

      if ( contents.get(guard) ) {
        ioh->doWrite(*(contents.get(guard)));
        nt = (ioh->builtin() || ioh->file())?
                EndpointNotification::FileData : EndpointNotification::SocketData;
      }
      return nt;
    }

    tuple<shared_ptr<Value>, EndpointNotification>
    refresh(shared_ptr<IOHandle> ioh)
    {
      strict_lock<LockB> guard(*this);
      EndpointNotification nt = EndpointNotification::NullEvent;
      
      // Read from the buffer (if possible)
      shared_ptr<Value> r;
      if ( contents.get(guard) ) { r = contents.get(guard); }

      // If there is more data in the underlying IOHandle
      // use it to populate the buffer
      if ( ioh->hasRead() ) {
        shared_ptr<Value> v = ioh->doRead();
        contents.get(guard) = v;
        nt = (ioh->builtin() || ioh->file())?
                EndpointNotification::FileData : EndpointNotification::SocketData;
      } 
      else {
        // Empty the buffer
        contents.get(guard) = shared_ptr<Value>();
      } 
      return make_tuple(r, nt);
    }

  protected:
    externally_locked<shared_ptr<Value>, ScalarEPBufferMT> contents;
  };


  class ContainerEPBufferST : public EndpointBuffer
  {
  public:
    typedef list<Value> BufferContents;

    ContainerEPBufferST(BufferSpec s) : spec(s)
    {
      contents = shared_ptr<BufferContents>(new BufferContents());
    }

    bool empty() { return contents? contents->empty() : true; }
    size_t size() { return contents? contents->size() : 0; }

    bool full() { 
      if ( !contents ) { return false; }
      int s = bufferMaxSize(spec);
      return s <= 0? false : contents->size() == s; 
    }
    
    size_t capacity() { 
      if ( !contents ) { return 0; }
      int s = bufferMaxSize(spec);
      return s <= 0 ? contents->max_size() : s;
    }

    // Appends to this buffer, returning the value if the append fails.
    shared_ptr<Value> append(shared_ptr<Value> v) {
      shared_ptr<Value> r;
      if ( contents ) {
        if ( this->full() ) { r = v; }
        else { contents->push_back(*v); }
      } else { r = v; }
      return r;
    }

    // TODO: Value vs Message
    // Transfers from this buffer into the given queues.
    void enqueue(shared_ptr<MessageQueues> queues) {
      if ( contents ) {
        for (auto v : *contents) { queues->enqueue(v); }
        contents->clear();
      }
    }

    // Writes the content of this buffer to the given IO handle. 
    // Returns a notification if the write is successfully performed.
    EndpointNotification flush(shared_ptr<IOHandle> ioh) 
    {
      EndpointNotification nt = EndpointNotification::NullEvent;
      if ( contents && batchAvailable() ) {
        bool written = false;
        for (int i = batchSize(); i > 0; --i) {
          auto v = contents->front();
          contents->pop_front();
          ioh->doWrite(v);
          written = true;
        }
        if ( written ) {
          nt = (ioh->builtin() || ioh->file())?
                  EndpointNotification::FileData : EndpointNotification::SocketData;
        }
      }
      return nt;
    }
    
    // Refresh this buffer by reading a value from the IO handle.
    // If the buffer is full, a value is returned. Also, a notification
    // is returned if the read is successfully performed.
    tuple<shared_ptr<Value>, EndpointNotification>
    refresh(shared_ptr<IOHandle> ioh)
    {
      EndpointNotification nt;
      shared_ptr<Value> r;

      if ( contents && !empty() ) { 
        // Grab first element from list, then remove it.
        // (pop_front has no return value)
        r = make_shared<Value>(contents->front());
        contents->pop_front();
      }
      if ( ioh->hasRead() ) {
        shared_ptr<Value> v = ioh->doRead();
        append(v);
        nt = (ioh->builtin() || ioh->file())?
                EndpointNotification::FileData : EndpointNotification::SocketData;
      }      
      return make_tuple(r, nt);      
    }

  protected:
    BufferSpec spec;
    shared_ptr<BufferContents > contents;

    int batchSize () { int r = bufferMaxSize(spec); return r <= 0? 1 : r; }
    bool batchAvailable() { return contents? contents->size() >= batchSize() : false; }

  };

  // This is form of buffer used in the C++ listener since we must use thread-safe buffers.
  // This is because we may have multiple threads handling a connection (e.g., with Boost Asio's io_service).
  class ContainerEPBufferMT : public EndpointBuffer, public basic_lockable_adapter<mutex>
  {
  public:
    typedef basic_lockable_adapter<mutex> bclockable;
    typedef ContainerEPBufferMT LockB;

    typedef list<Value> BufferContents;
    typedef externally_locked<shared_ptr<BufferContents>, ContainerEPBufferMT>
              ConcurrentBufferContents;
    
    ContainerEPBufferMT(BufferSpec s) : bclockable(), spec(s) {
      shared_ptr<BufferContents> cb = shared_ptr<BufferContents>(new BufferContents());
      contents = shared_ptr<ConcurrentBufferContents>(new ConcurrentBufferContents(*this, cb));
    }

    bool empty() { 
      strict_lock<LockB> guard(*this);
      return empty(guard);
    }

    bool full() {
      strict_lock<LockB> guard(*this);
      return full(guard);
    }

    size_t size() {
      strict_lock<LockB> guard(*this);
      size_t s = 0;
      if ( contents ) { s = contents->get(guard)->size(); }
      return s;
    }
    
    size_t capacity() {
      strict_lock<LockB> guard(*this);
      bool r = false;
      if ( contents ) {
        int s = bufferMaxSize(spec);
        r = s <= 0 ? contents->get(guard)->max_size() : s;
      }
      return r;
    }

    // Appends to this buffer, returning the value if the append fails.
    shared_ptr<Value> append(shared_ptr<Value> v) {      
      strict_lock<LockB> guard(*this);
      return append(guard, v);
    }

    // TODO: Value vs Message
    // Transfers from this buffer into the given queues.
    void enqueue(shared_ptr<MessageQueues> queues) {
      strict_lock<LockB> guard(*this);
      if ( contents ) {
        for (auto v : *(contents->get(guard))) { queues->enqueue(v); }
        contents->get(guard)->clear();
      }
    }

    // Writes the content of this buffer to the given IO handle. 
    // Returns a notification if the write is successfully performed.
    EndpointNotification flush(shared_ptr<IOHandle> ioh) 
    {
      EndpointNotification nt = EndpointNotification::NullEvent;
      strict_lock<LockB> guard(*this);
      
      if ( contents && batchAvailable(guard) ) {
        bool written = false;
        for (int i = batchSize(); i > 0; --i) {
          auto v = contents->get(guard)->front();
          contents->get(guard)->pop_front();
          
          ioh->doWrite(v);
          written = true;
        }
        if ( written ) {
          nt = (ioh->builtin() || ioh->file())?
                  EndpointNotification::FileData : EndpointNotification::SocketData;
        }
      }
      return nt;
    }
    
    // Refresh this buffer by reading a value from the IO handle.
    // If the buffer is full, a value is returned. Also, a notification
    // is returned if the read is successfully performed.
    tuple<shared_ptr<Value>, EndpointNotification>
    refresh(shared_ptr<IOHandle> ioh)
    {
      EndpointNotification nt = EndpointNotification::NullEvent;
      shared_ptr<Value> r;
      strict_lock<LockB> guard(*this);

      if ( contents && !empty(guard) ) { 
        r = make_shared<Value>(contents->get(guard)->front());
        contents->get(guard)->pop_front();
      }
      
      if ( ioh->hasRead() ) {
        shared_ptr<Value> v = ioh->doRead();
        append(guard, v);
        nt = (ioh->builtin() || ioh->file())?
                EndpointNotification::FileData : EndpointNotification::SocketData;
      }      
      return make_tuple(r, nt);      
    }

  protected:
    BufferSpec spec;
    shared_ptr<ConcurrentBufferContents> contents;

    int batchSize () { int r = bufferMaxSize(spec); return r <= 0? 1 : r; }
    bool batchAvailable(strict_lock<LockB>& guard) { return contents->get(guard)->size() >= batchSize(); }

    bool empty(strict_lock<LockB>& guard) {
      bool r = true;
      if ( contents ) { r = contents->get(guard)->empty(); }
      return r;
    }

    bool full(strict_lock<LockB>& guard) {
      bool r = false;
      if ( contents ) { 
        int s = bufferMaxSize(spec);
        r = s <= 0? false : contents->get(guard)->size() == batchSize(); 
      }
      return r;
    }

    // Appends to this buffer, returning the value if the append fails.
    shared_ptr<Value> append(strict_lock<LockB>& guard, shared_ptr<Value> v)
    {
      shared_ptr<Value> r;
      if ( contents ) {
        if ( this->full(guard) ) { r = v; }
        else { contents->get(guard)->push_back(*v); }
      }
      return r;        
    }

  };


  //----------------------------
  // I/O event notifications.

  class EndpointBindings : public LogMT
  {
  public:
    // TODO: value or value ref? Synchronize with Engine.hpp
    typedef std::function<void(const Address&,const Identifier&,const Value&)> SendFunctionPtr;

    typedef list<Message> Subscribers;
    typedef map<EndpointNotification, shared_ptr<Subscribers> > Subscriptions;

    EndpointBindings(SendFunctionPtr f) : LogMT("EndpointBindings"), sendFn(f) {}

    void attachNotifier(EndpointNotification nt, shared_ptr<Message> subscriber)
    {
      if ( subscriber ) {
        shared_ptr<Subscribers> s = eventSubscriptions[nt];
        if ( !s ) { 
          s = shared_ptr<Subscribers>(new Subscribers());
          eventSubscriptions[nt] = s;
        }

        s->push_back(*subscriber);
      }
      else { logAt(boost::log::trivial::error, "Invalid subscriber in notification registration"); } 
    }
    
    void detachNotifier(EndpointNotification nt, Identifier subId, Address subAddr)
    {
      auto it = eventSubscriptions.find(nt);
      if ( it != eventSubscriptions.end() ) {
        shared_ptr<Subscribers> s = it->second;
        if ( s ) { 
          s->remove_if(
            [&subId, &subAddr](const Message& m){
              return m.id() == subId && m.address() == subAddr;
            });
        }
      }
    }

    void notifyEvent(EndpointNotification nt)
    {
      auto it = eventSubscriptions.find(nt);
      if ( it != eventSubscriptions.end() ) {
        shared_ptr<Subscribers> s = it->second;
        if ( s ) {
          for (const Message& sub : *s) {
            sendFn(sub.address(), sub.id(), sub.contents());
          }
        }
      }
    }

  protected:
    SendFunctionPtr sendFn;
    Subscriptions eventSubscriptions;
  };
  


  //---------------------------------
  // Endpoints and their containers.

  class Endpoint
  {
  public:
    Endpoint(shared_ptr<IOHandle> ioh,
             shared_ptr<EndpointBuffer> buf,
             shared_ptr<EndpointBindings> subs)
      : handle_(ioh), buffer_(buf), subscribers_(subs)
    {
      buffer_->refresh(handle_); 
    }

    shared_ptr<IOHandle> handle() { return handle_; }
    shared_ptr<EndpointBuffer> buffer() { return buffer_; }
    shared_ptr<EndpointBindings> subscribers() { return subscribers_; }

    // An endpoint can be read if the handle can be read and the buffer isn't empty.
    bool hasRead() {
        return handle_->hasRead() || !buffer_->empty();
    }

    // An endpoint can be written to if the handle can be written to and the buffer isn't full.
    bool hasWrite() {
        return handle_->hasWrite() && !buffer_->full();
    }

    shared_ptr<Value> doRead() {
        // Refresh the buffer, getting back a read value, and an endpoint notification.
        tuple<shared_ptr<Value>, EndpointNotification> readResult = buffer_->refresh(handle_);

        // Notify those subscribers who need to be notified of the event.
        subscribers_->notifyEvent(get<1>(readResult));

        // Return the read result.
        return get<0>(readResult);
    }

    void doWrite(Value& v) {
        shared_ptr<Value> result = buffer_->append(v);

        if (result) {
            // TODO: Append failed, flush?
        } else {
            // TODO: Success, now what?
        }

        return;
    }

  protected:
    shared_ptr<IOHandle> handle_;
    shared_ptr<EndpointBuffer> buffer_;
    shared_ptr<EndpointBindings> subscribers_;
  };

  class EndpointState : public shared_lockable_adapter<shared_mutex>, public virtual LogMT
  {
  public:
    typedef shared_lockable_adapter<shared_mutex> eplockable;
    
    using ConcurrentEndpointMap =
      externally_locked<shared_ptr<EndpointMap, EndpointState>;

    using EndpointDetails = tuple<shared_ptr<IOHandle>, 
                                  shared_ptr<EndpointBuffer>,
                                  shared_ptr<EndpointBindings> >;

    EndpointState() 
      : eplockable(), LogMT("EndpointState"),
        internalEndpoints(emptyEndpointMap()),
        externalEndpoints(emptyEndpointMap())
    {}

    void addEndpoint(Identifier id, EndpointDetails details) {
      if ( !externalEndpointId(id) ) { 
        addEndpoint(id, details, internalEndpoints); 
      } else { 
        string errorMsg = "Invalid internal endpoint identifier";
        logAt(trivial::error, errorMsg);
        throw runtime_error(errorMsg);
      }
    }

    void addEndpoint(Identifier id, EndpointDetails details) {
      if ( externalEndpointId(id) ) {
        addEndpoint(id, details, externalEndpoints);
      } else {
        string errorMsg = "Invalid external endpoint identifier";
        logAt(trivial::error, errorMsg);
        throw runtime_error(errorMsg);
      }
    }

    void removeEndpoint(Identifier id) { 
      if ( !externalEndpointId(id) ) { 
        removeEndpoint(id, externalEndpoints);
      } else { 
        removeEndpoint(id, internalEndpoints);
      }
    }

    // TODO: endpoint id validation.
    shared_ptr<Endpoint> getInternalEndpoint(Identifier id) {
      return getEndpoint(id, internalEndpoints);
    }

    shared_ptr<Endpoint> getExternalEndpoint(Identifier id) {
      return getEndpoint(id, externalEndpoints);
    }

    size_t numEndpoints() {
      shared_lock_guard<EndpointState> guard(*this);
      return externalEndpoints->get(guard)->size() + internalEndpoints->get(guard)->size();
    }

  protected:
    shared_ptr<ConcurrentEndpointMap> internalEndpoints;
    shared_ptr<ConcurrentEndpointMap> externalEndpoints;

    shared_ptr<ConcurrentEndpointMap> emptyEndpointMap()
    {
      shared_ptr<EndpointMap> m = shared_ptr<EndpointMap>(new EndpointMap());
      return shared_ptr<ConcurrentEndpointMap>(new ConcurrentEndpointMap(*this, m));
    }


    void addEndpoint(Identifier id, EndpointDetails details,
                     shared_ptr<ConcurrentEndpointMap> epMap)
    {
      strict_lock<EndpointState> guard(*this);
      auto lb = epMap->get(guard)->lower_bound(id);
      if ( lb == epMap->get(guard)->end() || id != lb->first )
      {
        shared_ptr<Endpoint> ep =
          shared_ptr<Endpoint>(new Endpoint(get<0>(details), get<1>(details), get<2>(details)));

        epMap->get(guard)->insert(lb, make_pair(id, ep));
      } else {
        BOOST_LOG(*this) << "Invalid attempt to add a duplicate endpoint for " << id;
      }
    }

    void removeEndpoint(Identifier id, shared_ptr<ConcurrentEndpointMap> epMap)
    {
      strict_lock<EndpointState> guard(*this);
      epMap->get(guard)->erase(id);
    }

    shared_ptr<Endpoint> 
    getEndpoint(Identifier id, shared_ptr<ConcurrentEndpointMap> epMap)
    {
      shared_lock_guard<EndpointState> guard(*this);
      shared_ptr<Endpoint> r;
      auto it = epMap->get(guard)->find(id);
      if ( it != epMap->get(guard)->end() ) { r = it->second; }
      return r;
    }

  };


  //-------------------------------------
  // Connections and their containers.

  class ConnectionState : public shared_lockable_adapter<shared_mutex>,
                          public virtual LogMT
  {
  protected:
    // Connection maps are not thread-safe themselves, but are only
    // ever used by ConnectionState methods (which are thread-safe).
    class ConnectionMap : public virtual LogMT {
    public:
      ConnectionMap() : LogMT("ConnectionMap") {}
      
      ConnectionMap(shared_ptr<Net::NContext> ctxt)
        : LogMT("ConnectionMap"), context_(ctxt)
      {}

      bool addConnection(Address& addr, shared_ptr<Net::NConnection> c)
      {
        bool r = false;
        auto lb = cache.lower_bound(addr);
        if ( lb == cache.end() || addr != lb->first ) {
          auto it = cache.insert(lb, make_pair(addr, c));
          r = it->first == addr;
        } else {
          BOOST_LOG(*this) << "Invalid attempt to add a duplicate endpoint for " << addressAsString(addr);
        }
        return r;
      }

      shared_ptr<Net::NConnection> getConnection(Address& addr)
      {
        shared_ptr<Net::NConnection> r;
        try {
          r = cache.at(addr);
        } catch (const out_of_range& oor) {}
        if ( !r ) { BOOST_LOG(*this) << "No connection found for " << addressAsString(addr); }
        return r;
      }

      void removeConnection(Address& addr) { cache.erase(addr); }

      void clearConnections() { cache.clear(); }

      size_t size() { return cache.size(); }

    protected:
      shared_ptr<Net::NContext> context_;
      map<Address, shared_ptr<Net::NConnection> > cache;
    };

  public:
    typedef shared_lockable_adapter<shared_mutex> shlockable;
    
    typedef externally_locked<shared_ptr<ConnectionMap>, ConnectionState>
              ConcurrentConnectionMap;


    ConnectionState(shared_ptr<Net::NContext> ctxt)
      : shlockable(), LogMT("ConnectionState"),
        networkCtxt(ctxt),
        internalConnections(uninitializedConnectionMap()),
        externalConnections(emptyConnectionMap(ctxt))
    {}

    ConnectionState(shared_ptr<Net::NContext> ctxt, bool simulation) : ConnectionState(ctxt)
    {
      if ( !simulation ) { internalConnections = emptyConnectionMap(ctxt); }
    }

    void lock()          { shlockable::lock(); }
    void lock_shared()   { shlockable::lock_shared(); }
    void unlock()        { shlockable::unlock(); }
    void unlock_shared() { shlockable::unlock_shared(); }

    bool hasInternalConnections() {
      bool r = false;
      if ( internalConnections ) {
        strict_lock<ConnectionState> guard(*this);
        r = internalConnections->get(guard)? true : false;
      }
      return r;
    }

    shared_ptr<Net::NConnection> addConnection(Address addr, bool internal)
    {
      strict_lock<ConnectionState> guard(*this);
      shared_ptr<ConcurrentConnectionMap> cMap =
        internal? internalConnections : externalConnections;

      shared_ptr<Net::NConnection> conn =
        shared_ptr<Net::NConnection>(new Net::NConnection(networkCtxt, addr));
      
      return (cMap && cMap->get(guard)->addConnection(addr, conn))? conn : shared_ptr<Net::NConnection>();
    }

    void removeConnection(Address addr)
    {
      strict_lock<ConnectionState> guard(*this);
      shared_ptr<ConcurrentConnectionMap> cMap = mapForAddress(addr, guard);
      if ( cMap ) {
        cMap->get(guard)->removeConnection(addr);
      } else {
        BOOST_LOG(*this) << "No connection to " << addressAsString(addr) << " found for removal";
      }
    }
    
    void removeConnection(Address addr, bool internal)
    {
      strict_lock<ConnectionState> guard(*this);
      shared_ptr<ConcurrentConnectionMap> cMap = internal? internalConnections : externalConnections;
      if ( cMap ) {
        cMap->get(guard)->removeConnection(addr);
      } else {
        BOOST_LOG(*this) << "No connection to " << addressAsString(addr) << " found for removal";
      }      
    }

    // TODO: Ideally, this should be a shared lock.
    // TODO: investigate why does clang not like a shared_lock_guard here, while EndpointState::getEndpoint is fine.
    shared_ptr<Net::NConnection> getConnection(Address addr)
    {
      strict_lock<ConnectionState> guard(*this);
      shared_ptr<ConcurrentConnectionMap> cMap = mapForAddress(addr, guard);
      return getConnection(addr, cMap, guard);
    }

    // TODO: Ideally, this should be a shared lock.
    shared_ptr<Net::NConnection> getConnection(Address addr, bool internal) 
    {
      strict_lock<ConnectionState> guard(*this);
      shared_ptr<ConcurrentConnectionMap> cMap = internal? internalConnections : externalConnections;
      return getConnection(addr, cMap, guard);
    }

    // TODO
    virtual shared_ptr<Net::NConnection> getEstablishedConnection(Address addr) = 0;    
    virtual shared_ptr<Net::NConnection> getEstablishedConnection(Address addr, bool internal) = 0;

    void clearConnections() {
      strict_lock<ConnectionState> guard(*this);
      if ( internalConnections ) { internalConnections->get(guard)->clearConnections(); }
      if ( externalConnections ) { externalConnections->get(guard)->clearConnections(); }
    }
    
    void clearConnections(bool internal) {
      strict_lock<ConnectionState> guard(*this);
      shared_ptr<ConcurrentConnectionMap> cMap = 
        internal ? internalConnections : externalConnections;
      if ( cMap ) { cMap->get(guard)->clearConnections(); }
    };

    size_t numConnections() {
      strict_lock<ConnectionState> guard(*this);
      size_t r = 0;
      if ( internalConnections ) { r += internalConnections->get(guard)->size(); }
      if ( externalConnections ) { r += externalConnections->get(guard)->size(); }
      return r;
    }

  protected:
    shared_ptr<Net::NContext> networkCtxt;
    shared_ptr<ConcurrentConnectionMap> internalConnections;
    shared_ptr<ConcurrentConnectionMap> externalConnections;

    shared_ptr<ConcurrentConnectionMap> uninitializedConnectionMap() {
      return shared_ptr<ConcurrentConnectionMap>(new ConcurrentConnectionMap(*this));
    }

    shared_ptr<ConcurrentConnectionMap> 
    emptyConnectionMap(shared_ptr<Net::NContext> ctxt) 
    {
      shared_ptr<ConnectionMap> mp(new ConnectionMap(ctxt));
      return shared_ptr<ConcurrentConnectionMap>(new ConcurrentConnectionMap(*this, mp));
    }

    shared_ptr<ConcurrentConnectionMap> mapForId(Identifier& id) {
      return externalEndpointId(id) ? externalConnections : internalConnections;
    }

    // TODO: implement an alternative using a shared_lock_guard
    shared_ptr<ConcurrentConnectionMap>
    mapForAddress(Address& addr, strict_lock<ConnectionState>& guard)
    {
      shared_ptr<ConcurrentConnectionMap> r;
      if ( internalConnections && getConnection(addr, internalConnections, guard) ) {
        r = internalConnections;
        if ( !r && externalConnections && getConnection(addr, externalConnections, guard) ) {
          r = externalConnections;
        }
      }
      return r;
    }

    // TODO: implement an alternative using a shared_lock_guard
    shared_ptr<Net::NConnection>
    getConnection(Address& addr,
                  shared_ptr<ConcurrentConnectionMap> connections,
                  strict_lock<ConnectionState>& guard)
    {
      shared_ptr<Net::NConnection> r;
      if ( connections ) { r = connections->get(guard)->getConnection(addr); }
      return r;
    }
  };
}

#endif
