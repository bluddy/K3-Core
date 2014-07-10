#ifndef K3_RUNTIME_ENDPOINT_H
#define K3_RUNTIME_ENDPOINT_H

#include <list>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <memory>
#include <tuple>
#include <boost/thread/mutex.hpp>
#include <boost/thread/externally_locked.hpp>
#include <boost/thread/lockable_adapter.hpp>

#include <Common.hpp>
#include <Codec.hpp>
#include <Network.hpp>
#include <IOHandle.hpp>
#include <Queue.hpp>

// TODO: rewrite endpoint and connection containers without externally_locked as this requires a strict_lock.
// Ideally we want to use a shared_lock since the most common operation will be read accesses.

namespace K3
{
  typedef tuple<int, int> BufferSpec;

  enum class EndpointNotification {
    NullEvent, FileData, FileTick, FileClose, SocketAccept, SocketData, SocketTick, SocketClose
  };

  class BufferException : public runtime_error {
  public:
    BufferException(const std::string& msg) : runtime_error(msg) {}
    BufferException(const char* msg) : runtime_error(msg) {}
  };

  class EndpointException : public runtime_error {
  public:
    EndpointException(const std::string& msg) : runtime_error(msg) {}
    EndpointException(const char* msg) : runtime_error(msg) {}
  };

  typedef std::function<void(const Address&, const TriggerId, const Value&)> SendFunctionPtr;

  class Endpoint;
  typedef map<Identifier, Endpoint> EndpointMap;

  static inline int bufferMaxSize(BufferSpec& spec)   { return get<0>(spec); }
  static inline int bufferBatchSize(BufferSpec& spec) { return get<1>(spec); }

  static inline std::string internalEndpointPrefix() { return std::string("__");  }

  static inline Identifier connectionId(Address& addr) {
    return internalEndpointPrefix() + "_conn_" + addressAsString(addr);
  }

  static inline Identifier peerEndpointId(Address& addr) {
    return internalEndpointPrefix() + "_node_" + addressAsString(addr);
  }

  static inline bool externalEndpointId(Identifier& id) {
    std::string pfx = internalEndpointPrefix();
    return (mismatch(pfx.begin(), pfx.end(), id.begin()).first != pfx.end());
  }


  //------------------------
  // Endpoint buffers.
  // In contrast to the Haskell engine, in C++ we implement the concept of the
  // BufferContents datatype inline in the EndpointBuffer class. This is due
  // to the difference in the concurrency abstractions (e.g., MVar vs. externally_locked).

  class EndpointBuffer {
  public:
    typedef std::function<void(shared_ptr<Value>)> NotifyFn;

    EndpointBuffer() {}

    virtual bool empty() = 0;
    virtual bool full() = 0;
    virtual size_t size() = 0;
    virtual size_t capacity() = 0;

    // Appends to this buffer, returning if the append succeeds.
    virtual bool push_back(const Value& v) = 0;

    // Maybe Removes a value from the buffer and returns it
    virtual unique_ptr<Value> pop() = 0;

    // Attempt to pull a value from the provided IOHandle
    // into the buffer. Returns a Maybe Value
    virtual unique_ptr<Value> refresh(IOHandle&, NotifyFn) = 0;

    // Flush the contents of the buffer out to the provided IOHandle
    virtual void flush(IOHandle&, NotifyFn) = 0;

    // Transfer the contents of the buffer into provided MessageQueues
    // Using the provided InternalCodec to convert from Value to Message
    virtual bool transfer(MessageQueues&, InternalCodec&, NotifyFn)= 0;
  };


  class ScalarEPBufferMT : public EndpointBuffer, public boost::basic_lockable_adapter<boost::mutex> {
  public:
    typedef ScalarEPBufferMT LockB;

    ScalarEPBufferMT() : contents(*this) {}

    bool empty() {
      boost::strict_lock<LockB> guard(*this);
      return contents.get(guard).second;
    }
    bool   full()     { return !empty(); }
    size_t size()     { return full() ? 1 : 0; }
    size_t capacity() { return 1; }

    // Buffer Operations
    void push_back(Value& v) {
      strict_lock<LockB> guard(*this);
      contents.get(guard).first = v;
      contents.get(guard).second = false;
    }

    unique_ptr<Value> pop() {
      strict_lock<LockB> guard(*this);
      if (contents.get(guard).second) { return NULL };
      Value ret = new Value(contents.get(guard).first);
      contents.get(guard).first = "";
      contents.get(guard).second = true;
      return ret;
    }

    unique_ptr<Value> refresh(IOHandle& ioh, NotifyFn notify);

    void flush(IOHandle& ioh, NotifyFn notify);

    bool transfer(MessageQueues& queues, InternalCodec& cdec, NotifyFn notify);

   protected:
    // bool is empty
    boost::externally_locked<pair<Value, bool>>, LockB> contents_;
  };

  class ScalarEPBufferST : public EndpointBuffer {
  public:
    ScalarEPBufferST() {}
    // Metadata
    bool   empty()    { return empty_; }
    bool   full()     { return !empty(); }
    size_t size()     { return full() ? 1 : 0; }
    size_t capacity() { return 1; }

    // Buffer Operations
    bool push_back(const Value& v);

    unique_ptr<Value> pop();

    unique_ptr<Value> refresh(IOHandle& ioh, NotifyFn notify);

    void flush(IOHandle& ioh, NotifyFn notify);

    bool transfer(MessageQueues& queues, InternalCodec& cdec, NotifyFn notify);

   protected:
    Value contents_;
    bool empty_;
  };

  class ContainerEPBufferST : public EndpointBuffer {
  public:
    ContainerEPBufferST(BufferSpec s) : spec_(s) { }

    bool   empty() { return contents_.empty(); }
    bool   full()  { return size() >= bufferMaxSize(spec_); }
    size_t size()  { return empty() ? 0 : contents_.size(); }
    size_t capacity();

    bool push_back(Value& v);

    unique_ptr<Value> pop();

    unique_ptr<Value> refresh(IOHandle& ioh, NotifyFn notify);

    // Default flush: do not force, wait for batch
    void flush(IOHandle& ioh, NotifyFn notify) { flush(ioh, notify, false); }

    // flush overloaded with force flag to ignore batching semantics
    void flush(IOHandle& ioh, NotifyFn notify, bool force);

    // Default transfer: do not force, wait for batch
    bool transfer(MessageQueues& queues, InternalCodec& cdec, NotifyFn notify) {
      return transfer(queues, cdec, notify, false);
    }

    // transfer overloaded with force flag to ignore batching semantics
    bool transfer(MessageQueues& queues, InternalCodec& cdec, NotifyFn notify, bool force);

   protected:
    vector<Value> contents_;
    BufferSpec spec_;

    int batchSize() { int r = bufferMaxSize(spec); return r <=0 ? 1 : r;}
    bool batchAvailable() { return contents ? contents->size() >= batchSize(): false;}
  };

  //----------------------------
  // I/O event notifications.

  class EndpointBindings : public LogMT {
  public:

    // address, trigger subscribed
    typedef unordered_set<pair<Address, TriggerId>> Subscribers;

    typedef unordered_map<EndpointNotification, Subscribers> Subscriptions;

    EndpointBindings(SendFunctionPtr f) : LogMT("EndpointBindings"), sendFn_(f) {}

    void attachNotifier(EndpointNotification nt, Address sub_addr, TriggerId sub_id);

    void detachNotifier(EndpointNotification nt, Address sub_addr, TriggerId sub_id);

    void notifyEvent(EndpointNotification nt, shared_ptr<Value> payload);

  protected:
    SendFunctionPtr sendFn_;
    Subscriptions eventSubscriptions_;
  };

  //---------------------------------
  // Endpoints and their containers.

  class Endpoint
  {
  public:
    Endpoint(unique_ptr<IOHandle> ioh,
             unique_ptr<EndpointBuffer> buf,
             unique_ptr<EndpointBindings> subs)
      : handle_(std::move(ioh)), buffer_(std::move(buf)), 
        subscribers_(std::move(subs))
    {
      if (handle_->isInput()) { refreshBuffer(); }
    }

    IOHandle& handle()              { return handle_; }
    EndpointBuffer& buffer()        { return buffer_; }
    EndpointBindings& subscribers() { return subscribers_; }

    void notify_subscribers(Value& v);

    // An endpoint can be read if the handle can be read or the buffer isn't empty.
    bool hasRead() { return handle_->hasRead() || !buffer_->empty(); }

    // An endpoint can be written to if the handle can be written to and the buffer isn't full.
    bool hasWrite() { return handle_->hasWrite() && !buffer_->full(); }

    unique_ptr<Value> refreshBuffer();

    void flushBuffer();

    unique_ptr<Value> doRead() { return refreshBuffer(); }

    void doWrite(Value& v);

    bool do_push(Value& val, MessageQueues& q, InternalCodec& codec);

    // Closes the endpoint's IOHandle, while also notifying subscribers
    // of the close event.
    void close();;

  protected:
    unique_ptr<IOHandle> handle_;
    unique_ptr<EndpointBuffer> buffer_;
    unique_ptr<EndpointBindings> subscribers_;
  };


  // TODO: switch endpointmap to contain endpoints and return references
  // Nobody else owns endpoints

  class EndpointState : public boost::basic_lockable_adapter<boost::mutex>
  {
  public:
    typedef boost::basic_lockable_adapter<boost::mutex> eplockable;

    using ConcurrentEndpointMap =
      boost::externally_locked<EndpointMap, EndpointState>;

    using EndpointDetails = tuple<shared_ptr<IOHandle>,
                                 shared_ptr<EndpointBuffer>,
                                 shared_ptr<EndpointBindings> >;

    EndpointState()
      : eplockable(),
        epsLogger_(LogMT("EndpointState"))
    {}

    void addEndpoint(Identifier id, EndpointDetails details) {
      if (externalEndpointId(id)) {
        addEndpoint(id, details, externalEndpoints);
      } else {
        addEndpoint(id, details, internalEndpoints);
      }
    }

    void removeEndpoint(Identifier id) {
      if (externalEndpointId(id)) {
        removeEndpoint(id, externalEndpoints);
      } else {
        removeEndpoint(id, internalEndpoints);
      }
    }

    void clearEndpoints() {
      clearEndpoints(internalEndpoints_);
      clearEndpoints(externalEndpoints_);
      return;
    }

    void clearEndpoints(ConcurrentEndpointMap& m);

    // Pointer has no ownership
    Endpoint* getInternalEndpoint(const Identifier& id);

    // Pointer has no ownership
    Endpoint* getExternalEndpoint(const Identifier& id);

    size_t numEndpoints();

    void logEndpoints();

  protected:
    LogMT epsLogger_;
    ConcurrentEndpointMap internalEndpoints_;
    ConcurrentEndpointMap externalEndpoints_;

    void addEndpoint(Identifier id, EndpointDetails details,
                     ConcurrentEndpointMap& epMap);

    void removeEndpoint(Identifier id, ConcurrentEndpointMap& epMap)
    {
      boost::strict_lock<EndpointState> guard(*this);
      epMap.get(guard).erase(id);
    }

    void EndpointState::clearEndpoints(ConcurrentEndpointMap& m) {
      boost::strict_lock<EndpointState> guard(*this);
      m.clear();
    }

    // TODO: allow direct access to endpoints (saving them) so we don't have to
    // keep going through the map
    Endpoint* getEndpoint(Identifier id, ConcurrentEndpointMap& epMap);
  };


  ////-------------------------------------
  //// Connections and their containers.

  class ConnectionState : public boost::shared_lockable_adapter<boost::shared_mutex>, public virtual LogMT
  {
  protected:
    // Connection maps are not thread-safe themselves, but are only
    // ever used by ConnectionState methods (which are thread-safe).
    class ConnectionMap : public virtual LogMT {
    public:
      ConnectionMap(Net::NContext& ctxt): LogMT("ConnectionMap"), context_(ctxt) {}

      bool addConnection(Address& addr, const Net::NConnection& c);

      // no ownership return
      Net::NConnection* getConnection(Address& addr);

      void removeConnection(Address& addr) { cache.erase(addr); }

      void clearConnections() { cache_.clear(); }

      size_t size() { return cache_.size(); }

    protected:
      Net::NContext& context_; // owned by outside
      unordered_map<Address, Net::NConnection> cache_;
   };

  public:
    typedef boost::shared_lockable_adapter<boost::shared_mutex> shlockable;

    typedef boost::externally_locked<ConnectionMap, ConnectionState> ConcurrentConnectionMap;

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

    bool hasInternalConnections();

    shared_ptr<Net::NConnection> addConnection(Address addr, bool internal);

    void removeConnection(Address addr);

    void removeConnection(Address addr, bool internal);

    // TODO: Ideally, this should be a shared lock.
    // TODO: investigate why does clang not like a shared_lock_guard here, while EndpointState::getEndpoint is fine.
    shared_ptr<Net::NConnection> getConnection(Address addr);

    // TODO: Ideally, this should be a shared lock.
    shared_ptr<Net::NConnection> getConnection(Address addr, bool internal);

    // TODO
    // virtual shared_ptr<Net::NConnection> getEstablishedConnection(Address addr) = 0;
    // virtual shared_ptr<Net::NConnection> getEstablishedConnection(Address addr, bool internal) = 0;

    void clearConnections();

    void clearConnections(bool internal);

    size_t numConnections();

  protected:
    shared_ptr<Net::NContext> networkCtxt;
    shared_ptr<ConcurrentConnectionMap> internalConnections;
    shared_ptr<ConcurrentConnectionMap> externalConnections;

    shared_ptr<ConcurrentConnectionMap> uninitializedConnectionMap() {
      return shared_ptr<ConcurrentConnectionMap>(new ConcurrentConnectionMap(*this));
    }

    shared_ptr<ConcurrentConnectionMap>
    emptyConnectionMap(shared_ptr<Net::NContext> ctxt);

    shared_ptr<ConcurrentConnectionMap> mapForId(Identifier& id) {
      return externalEndpointId(id) ? externalConnections : internalConnections;
    }

    // TODO: implement an alternative using a shared_lock_guard
    shared_ptr<ConcurrentConnectionMap>
    mapForAddress(Address& addr, boost::strict_lock<ConnectionState>& guard);

    // TODO: implement an alternative using a shared_lock_guard
    shared_ptr<Net::NConnection>
    getConnection(Address& addr,
                  shared_ptr<ConcurrentConnectionMap> connections,
                  boost::strict_lock<ConnectionState>& guard);
  };
};

#endif
// vim: set sw=2 ts=2 sts=2:
