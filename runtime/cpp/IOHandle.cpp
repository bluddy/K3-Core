#include "IOHandle.hpp"

namespace K3
{
    string IStreamHandle::doRead() {
      string result;

      while (result != "") {
        if (codec->decode_ready()) {
          // return a buffered value if possible
          result = codec->decode("");
        }
        else if (input_->good()) {
          // no buffered values: grab data from stream
          char buffer[1024];
          input_->read(buffer,sizeof(buffer));
          string s = string(buffer);
          // use the new data to attempt a decode.
          // if it fails: continue the loop
          result = codec->decode(s);
        }
        else {
          // Failure: ran out of buffered values and stream data
          BOOST_LOG(*this) << "doRead: Stream has been exhausted, and no values in buffer";
        }
      }
      return result;
    }
} // namespace K3
