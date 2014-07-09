#ifndef K3_RUNTIME_IOHANDLE_HPP
#define K3_RUNTIME_IOHANDLE_HPP

#include <memory>
#include <boost/iostreams/device/file.hpp>
#include <boost/iostreams/filtering_stream.hpp>
#include <boost/iostreams/filter/line.hpp>

#include "Common.hpp"
#include "Codec.hpp"
#include "Network.hpp"

namespace K3
{
  //--------------------------
  // IO handles

  class IOHandle : public virtual LogMT
  {
  public:
    typedef tuple<shared_ptr<Codec>, shared_ptr<Net::NEndpoint> > SourceDetails;
    typedef tuple<shared_ptr<Codec>, shared_ptr<Net::NConnection> > SinkDetails;

    IOHandle(shared_ptr<Codec> cdec) : LogMT("IOHandle"), codec(cdec) {}

    virtual bool isInput() = 0;
    virtual bool isOutput() = 0;
    virtual bool hasRead() = 0;
    virtual unique_ptr<Value> doRead() = 0;

    virtual bool hasWrite() = 0;
    virtual void doWrite(const Value& v) = 0;

    virtual void close() = 0;

    virtual bool builtin() = 0;
    virtual bool file() = 0;

    virtual SourceDetails networkSource() = 0;
    virtual SinkDetails networkSink() = 0;

  protected:
    shared_ptr<Codec> codec;
  };

  class IStreamHandle : public virtual LogMT
  {
  public:
    template<typename Source>
    IStreamHandle(shared_ptr<Codec> cdec, Source& src)
      : LogMT("IStreamHandle"), codec(cdec)
    {
      input_.push(src);
    }

    bool hasRead() {
        return (input_.good() && codec->good()) || codec->decode_ready();
    }

    unique_ptr<string> doRead();

    bool hasWrite() {
      BOOST_LOG(*this) << "Invalid write operation on input handle";
      return false;
    }

    void doWrite(const Value &data) {
      BOOST_LOG(*this) << "Invalid write operation on input handle";
    }

    // Invoke the destructor on the filtering_istream, which in
    // turn closes all associated iostream filters and devices.
    void close() { input_.reset(); }

  protected:
    filtering_istream input_;
    shared_ptr<Codec> codec;
  };

  class OStreamHandle : public virtual LogMT
  {
  public:
    template<typename Sink>
    OStreamHandle(shared_ptr<Codec> cdec, Sink& sink)
      : LogMT("OStreamHandle"), codec(cdec)
    {
      output.push(sink);
    }

    bool hasRead() {
      BOOST_LOG(*this) << "Invalid read operation on output handle";
      return false;
    }

    unique_ptr<Value> doRead() {
      BOOST_LOG(*this) << "Invalid read operation on output handle";
      return unique_ptr<Value>();
    }

    bool hasWrite() { return output.good(); }

    void doWrite(const Value& data ) { output << codec->encode(data); }

    void close() { output.reset(); }

  protected:
    filtering_ostream output;
    shared_ptr<Codec> codec;
  };

  // TODO: refactor this so stream input/output inherit from this
  class StreamHandle : public IOHandle
  {
  public:
    // TODO: change to enums
    struct Input  {};
    struct Output {};

    template<typename Source>
    StreamHandle(shared_ptr<Codec> cdec, Input i, Source& src)
      : LogMT("StreamHandle"), IOHandle(cdec), isInput_(true),
        inImpl(unique_ptr<IStreamHandle>(new IStreamHandle(cdec, src)))
    { }

    template<typename Sink>
    StreamHandle(shared_ptr<Codec>  cdec, Output o, Sink& sink)
      : LogMT("StreamHandle"), IOHandle(cdec), isInput_(false),
        outImpl(unique_ptr<OStreamHandle>(new OStreamHandle(cdec, sink)))
    { }

    bool isInput()  { return isInput_; }
    bool isOutput() { return !isInput_; }

    // There are slightly bigger problems with the entire StreamHandle class
    // that makes it difficult to have one that does both input and output

    bool hasRead()  {
      bool r = false;
      if (inImpl) { r = inImpl->hasRead(); }
      else { BOOST_LOG(*this) << "Invalid hasRead on LineBasedHandle"; }
      return r;
    }

    bool hasWrite() {
      bool r = false;
      if (outImpl) { r = outImpl->hasWrite(); }
      else { BOOST_LOG(*this) << "Invalid hasWrite on LineBasedHandle"; }
      return r;
    }

    unique_ptr<Value> doRead() {
      unique_ptr<Value> data;
      if (inImpl) {
        data = inImpl->doRead();
      }
      else { BOOST_LOG(*this) << "Invalid doRead on LineBasedHandle"; }
      return data;
    }

    void doWrite(Value& v) {
      if (outImpl) {
        outImpl->doWrite(v);
      }
      else { BOOST_LOG(*this) << "Invalid doWrite on LineBasedHandle"; }
    }

    void close() {
      if (inImpl) { inImpl->close(); }
      else if (outImpl) { outImpl->close(); }
    }

  protected:
    unique_ptr<IStreamHandle> inImpl;
    unique_ptr<OStreamHandle> outImpl;
    bool isInput_;
  };


  class BuiltinHandle : public StreamHandle
  {
  public:
    // TODO: change to enums
    struct Stdin  {};
    struct Stdout {};
    struct Stderr {};

    BuiltinHandle(shared_ptr<Codec> cdec, Stdin s)
      : LogMT("BuiltinHandle"), StreamHandle(cdec, StreamHandle::Input(), cin)
    {}

    BuiltinHandle(shared_ptr<Codec> cdec, Stdout s)
      : LogMT("BuiltinHandle"), StreamHandle(cdec, StreamHandle::Output(), cout)
    {}

    BuiltinHandle(shared_ptr<Codec> cdec, Stderr s)
      : LogMT("BuiltinHandle"), StreamHandle(cdec, StreamHandle::Output(), cerr)
    {}

    bool isInput()  { return isInput_; }
    bool isOutput() { return !isInput_; }
    bool builtin () { return true; }
    bool file()     { return false; }

    IOHandle::SourceDetails networkSource()
    {
      return make_tuple(shared_ptr<Codec>(), shared_ptr<Net::NEndpoint>());
    }

    IOHandle::SinkDetails networkSink()
    {
      return make_tuple(shared_ptr<Codec>(), shared_ptr<Net::NConnection>());
    }
  };

  class FileHandle : public StreamHandle
  {
  public:
    FileHandle(shared_ptr<Codec> cdec, const file_sink &fs, StreamHandle::Input i)
      : StreamHandle(cdec, i, fs), LogMT("FileHandle")
    {}

    FileHandle(shared_ptr<Codec> cdec, const file_sink &fs, StreamHandle::Output o)
      : StreamHandle(cdec, o, fs), LogMT("FileHandle")
    {}

    bool builtin()  { return false; }
    bool file()     { return true; }

    IOHandle::SourceDetails networkSource()
    {
      return make_tuple(shared_ptr<Codec>(), shared_ptr<Net::NEndpoint>());
    }

    IOHandle::SinkDetails networkSink()
    {
      return make_tuple(shared_ptr<Codec>(), shared_ptr<Net::NConnection>());
    }
  };

  // TODO: subclass into connection and endpoint
  class NetworkHandle : public IOHandle
  {
  public:
    NetworkHandle(shared_ptr<Codec> cdec, unique_ptr<Net::NConnection> c)
      : LogMT("NetworkHandle"), connection(std::move(c)), IOHandle(cdec), isInput_(false)
    {}

    NetworkHandle(shared_ptr<Codec> cdec, unique_ptr<Net::NEndpoint> e)
      : LogMT("NetworkHandle"), endpoint(std::move(e)), IOHandle(cdec), isInput_(false)
    {}

    bool isInput()  { return isInput_; }
    bool isOutput() { return !isInput_; }
    bool hasRead()  {
      BOOST_LOG(*this) << "Invalid hasRead on NetworkHandle";
      return false;
    }

    bool hasWrite() {
      bool r = false;
      if (connection) {
        r = connection->connected(); }
      else { BOOST_LOG(*this) << "Invalid hasWrite on NetworkHandle"; }
      return r;
    }

    unique_ptr<Value> doRead() {
      BOOST_LOG(*this) << "Invalid doRead on NetworkHandle";
      return unique_ptr<Value>();
    }

    void doWrite(Value&  v) {
      if (connection && codec) {
        auto data = codec->encode(v);
        connection->write(data);
      }
      else {
        BOOST_LOG(*this) << "Invalid doWrite on NetworkHandle";
      }
    }

    void close() {
      if (connection) { connection->close(); }
      else if (endpoint) { endpoint->close(); }
    }

    bool builtin () { return false; }
    bool file() { return false; }

    IOHandle::SourceDetails networkSource()
    {
      shared_ptr<Codec> cdec = endpoint? codec : shared_ptr<Codec>();
      return make_tuple(cdec, endpoint);
    }

    IOHandle::SinkDetails networkSink()
    {
      shared_ptr<Codec> cdec = connection? codec : shared_ptr<Codec>();
      return make_tuple(cdec, connection);
    }

  protected:
    unique_ptr<Net::NConnection> connection;
    unique_ptr<Net::NEndpoint>   endpoint;
    bool isInput_;
  };

} // namespace K3

#endif // K3_RUNTIME_IOHANDLE_HPP
