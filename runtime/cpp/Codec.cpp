#include <cstdlib>
#include "Common.hpp"
#include "Codec.hpp"

using namespace std;

namespace K3 {

      Value DelimiterCodec::encode(const Value& v) {
        string res = string(v);
        res.push_back(delimiter_);
        return res;
      }

      Value DelimiterCodec::decode(const Value& v) {

        // Append to buffer
        buf_.append(v);
        // Determine if there is a complete value in the buffer
        Value result = "";
        size_t pos = find_delimiter();
        if (pos != std::string::npos) {
          // There is a complete value
          // Grab it from the buffer
          result = buf_->substr(0, pos); // ignore the delimiter at pos
          // Delete from the buffer
          buf_ = buf_->substr(pos+1);
        }
        return result;
      }

      Value LengthHeaderCodec::encode(const Value& s) {
        // calculate size of encoded value
        fixed_int value_size = fixed_int(s.length());
        size_t header_size = sizeof(value_size);
        size_t enc_size = header_size + value_size;
        // pack data into a buffer
        string result;
        result.resize(enc_size);
        memcpy(result.c_str(), &value_size, header_size);
        memcpy(result.c_str() + header_size, s.c_str(), value_size);

        return result;
      }

      Value LengthHeaderCodec::decode(const Value& v) {

        if (v != "") {
          buf_ = buf_ + v;
        }

        if (!have_size_) {
          // See if there is enough data in buffer to unpack a header
          strip_header();
          if (!have_size_) {
            // failure: not enough data in buffer
            return Value("");
          }
        }

        // Now that we know the size of the next incoming value
        // See if the buffer contains enough data to unpack
        if (decode_ready()) {
          // Unpack next value
          const char * bytes = buf_.c_str();
          Value result(bytes, next_size_);

          // Setup for next round
          *buf_ = buf_->substr(next_size_);
          have_next_size_ = false;
          return result;
        }
        else {
          // failure: not enough data in buffer
          return Value("");
        }
      }

      void LengthHeaderCodec::strip_header() {
        size_t header_size = sizeof(fixed_int);
        if (buf_.length() < header_size) {
          // failure: input does not contain a full header
          return;
        }

        // copy the fixed_int into next_size_
        memcpy(&next_size_, buf_.c_str(), header_size);
        have_size_ = true;

        // remove the header bytes from the buffer
        buf_ = buf_->substr(header_size);
      }

      RemoteMessage AbstractDefaultInternalCodec::read_message(const Value& v) {
        // Values are of the form: "(Address, Identifier, Payload)"
        // Split value into components:
        static const boost::regex value_regex("\\( *(.+) *, *(.+) *, *(.+) *\\)");
        boost::cmatch value_match;
        if(boost::regex_match(v.c_str(), value_match, value_regex)){
          // Parse Address
          static const boost::regex address_regex("(.+):(.+)");
          boost::cmatch address_match;
          Address a;
          string temp = value_match[1];
          if(boost::regex_match(temp.c_str(), address_match, address_regex)) {
            string ip = address_match[1];
            temp = address_match[2];
            unsigned short port = (unsigned short) std::strtoul(temp.c_str(), NULL, 0);
            a = make_address(ip, port);
          }
          else {
            throw CodecException("Invalid Format for Value's Address: " + value_match[1]);
          }

          // Parse Identifier
          string temp2 = value_match[2];
          TriggerId id = atoi(temp2.c_str());

          // Parse Payload
          Value payload = value_match[3];
          return RemoteMessage(a, id, payload);
         }
        else {
          throw CodecException("Invalid Format for Value:" + v);
        }
      }

      Value AbstractDefaultInternalCodec::show_message(const RemoteMessage& m) {
        ostringstream os;
        os << "(" << addressAsString(m.address()) << "," << m.id() << "," << m.contents() << ")";
        string s = os.str();
        return s;
      }
} // namespace K3

