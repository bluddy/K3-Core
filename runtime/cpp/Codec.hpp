#ifndef K3_RUNTIME_CODEC_H
#define K3_RUNTIME_CODEC_H

#include <string>

#include "Message.hpp"

namespace K3 {

  //--------------------
  // Wire descriptions

  // A generic exception that can be thrown by wire descriptor methods.
  class CodecException : public std::runtime_error {
  public:
    CodecException(const std::string& msg) : runtime_error(msg) {}
    CodecException(const char* msg) : runtime_error(msg) {}
  };

  // Message serializtion/deserialization abstract base class.
  // Implementations can encapsulate framing concerns as well as serdes operations.
  //
  // The unpack method may be supplied a complete or incomplete std::string corresponding
  // to a value. It is left to the implementation to determine the scope of functionality
  // supported, for example partial unpacking (e.g., for network sockets).
  // The semantics of repeated invocations are dependent on the actual implementation
  // of the wire description (including factors such as message loss).
  // This includes the conditions under which an exception is thrown.

  class Codec: public virtual LogMT {
    public:
      Codec(): LogMT("Codec") {}

      virtual Value encode(const Value&) = 0;
      virtual Value decode(const Value&) = 0;
      virtual bool decode_ready() = 0;
      virtual bool good() = 0;

      // codec cloning
      virtual ~Codec() {}
      virtual std::shared_ptr<Codec> freshClone() = 0;

  };

  class DefaultCodec : public virtual Codec, public virtual LogMT {
    public:
      DefaultCodec() : Codec(), LogMT("DefaultCodec"), good_(true) {}

      Value encode(const Value& v) { return v; }

      Value decode(const Value& v) { return v; }

      bool decode_ready() { return true; }

      bool good() { return good_; }

      std::shared_ptr<Codec> freshClone() {
        return std::make_shared<DefaultCodec>();
      };

    protected:
      bool good_;
  };

  class InternalCodec: public virtual Codec {
    public:
      InternalCodec() : LogMT("InternalCodec") {}

      virtual RemoteMessage read_message(const Value&) = 0;
      virtual Value show_message(const RemoteMessage&) = 0;
  };

  class DelimiterCodec : public virtual Codec, public virtual LogMT {
    public:
      DelimiterCodec(char delimiter)
        : Codec(), LogMT("DelimiterCodec"), delimiter_(delimiter), good_(true)
      {}

      Value encode(const Value& v);

      Value decode(const Value& v);

      bool decode_ready() {
          return (find_delimiter() != std::string::npos);
      }

      bool good() { return good_; }

      std::shared_ptr<Codec> freshClone() {
        return std::make_shared<DelimiterCodec>(delimiter_);
      }

      char delimiter_;
    protected:
      size_t find_delimiter() { return buf_.find(delimiter_); }
      bool good_;
      std::string buf_;
  };

  class LengthHeaderCodec : public virtual Codec, public virtual LogMT {
    public:
      LengthHeaderCodec()
        : Codec(), LogMT("LengthHeaderCodec"), good_(true),
          next_size_(0), have_size_(false)
      {}

      Value encode(const Value& s);

      Value decode(const Value& v);

      bool decode_ready() {
        return have_size_ ? buf_.length() >= next_size_ : false;
      }

      bool good() { return good_; }

      std::shared_ptr<Codec> freshClone() {
        return std::make_shared<LengthHeaderCodec>();
      };

    protected:
      bool good_;
      bool have_size_;
      fixed_int next_size_;
      std::string buf_;

      void strip_header();
  };

  class AbstractDefaultInternalCodec : public virtual InternalCodec, public virtual LogMT {
    public:
      AbstractDefaultInternalCodec() : InternalCodec(), LogMT("AbstractDefaultInternalCodec") {}

      RemoteMessage read_message(const Value& v);

      Value show_message(const RemoteMessage& m);
  };

  class DefaultInternalCodec : public AbstractDefaultInternalCodec, public DefaultCodec, public virtual LogMT {
    public:
      DefaultInternalCodec()
        : AbstractDefaultInternalCodec(), DefaultCodec(), LogMT("DefaultInternalCodec")
      {}

      std::shared_ptr<Codec> freshClone() {
        return std::make_shared<DefaultInternalCodec>();
      }

  };

  class DelimiterInternalCodec : public AbstractDefaultInternalCodec, public DelimiterCodec, public virtual LogMT {
    public:
      DelimiterInternalCodec(char delimiter)
        : AbstractDefaultInternalCodec(), DelimiterCodec(delimiter), LogMT("DelimiterInternalCodec")
      {}

      std::shared_ptr<Codec> freshClone() {
        return std::make_shared<DelimiterInternalCodec>(delimiter_);
      }
  };

  class LengthHeaderInternalCodec : public AbstractDefaultInternalCodec, public LengthHeaderCodec, public virtual LogMT {
    public:
      LengthHeaderInternalCodec()
        : AbstractDefaultInternalCodec(), LengthHeaderCodec(), LogMT("LengthHeaderInternalCodec")
      {}

      std::shared_ptr<Codec> freshClone() {
        return std::make_shared<LengthHeaderInternalCodec>();
      }
  };

  using ExternalCodec = Codec;

} // namespace K3

#endif // K3_RUNTIME_CODEC_H
