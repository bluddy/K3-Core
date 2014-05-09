// The K3 Runtime Collections Library.
//
// This file contains definitions for the various operations performed on K3 collections, used by
// the generated C++ code. The C++ realizations of K3 Collections will inherit from the
// K3::Collection class, providing a suitable content type.
//
// TODO:
//  - Use <algorithm> routines to perform collection transformations? In particular, investigate
//    order-of-operations semantics.
//  - Use container agnostic mutation operations?
//  - Use bulk mutation operations (iterator-based insertion, for example)?
//  - Optimize all the unnecessary copies, using std::move?
#ifndef K3_RUNTIME_COLLECTIONS_H
#define K3_RUNTIME_COLLECTIONS_H

#include <functional>
#include <list>
#include <map>
#include <memory>
#include <tuple>

#include <Engine.hpp>
#include <dataspace/StlDS.hpp>
#include <dataspace/SetDS.hpp>
#include <dataspace/ListDS.hpp>
#include <dataspace/SortedDS.hpp>
#include <boost/serialization/base_object.hpp>

namespace K3 {
  template <template <class...> class D, class E>
  class Collection: public D<E> {
    public:
      Collection(Engine * e) : D<E>(e) {}

      template <template <class> class F>
      Collection(const Collection<F, E> other) : D<E>(other)  {}

      template <template <class> class F>
      Collection(Collection<F, E>&& other) : D<E>(other) {}

      Collection(D<E> other) : D<E>(other) {}

      std::shared_ptr<E> peek() { return D<E>::peek(); }

      void insert(const E& elem) { D<E>::insert(elem); }
      void insert(E&& elem) { D<E>::insert(elem); }

      void erase(const E& elem)  { D<E>::erase(elem); }

      void update(const E& v1, const E& v2) { D<E>::update(v1,v2); }
      void update(const E& v1, E&& v2) { D<E>::update(v1,v2); }

      std::tuple<Collection<D, E>, Collection<D, E>> split() {
        auto tup = D<E>::split();
        D<E> ds1 = get<0>(tup);
        D<E> ds2 = get<1>(tup);
        return std::make_tuple(Collection<D,E>(ds1), Collection<D,E>(ds2));
      }

      template <template <class> class F>
      Collection<D, E> combine(const Collection<F, E>& other) {
       return Collection<D,E>(D<E>::combine(other));
      }

      template <class T>
      Collection<D, T> map(std::function<T(E)> f) {
       return Collection<D,T>(D<E>::map(f));
      }

      Collection<D, E> filter(std::function<bool(E)> f) {
       return Collection<D,E>(D<E>::filter(f));
      }
   
      template <class Z>
      Z fold(std::function<Z(Z, E)> f, Z init) {
       return D<E>::fold(f, init);
      }

      template <class K, class Z>
      Collection<D, std::tuple<K, Z>> group_by(
        std::function<K(E)> grouper, std::function<Z(Z, E)> folder, Z init) {
          // Create a map to hold partial results
          std::map<K, Z> accs = std::map<K,Z>();
          // lambda to apply to each element
          std::function<void(E)> f = [&] (E elem) {
            K key = grouper(elem);
            if (accs.find(key) == accs.end()) {
              accs[key] = init;
            }
            accs[key] = folder(accs[key], elem);
          };
          D<E>::iterate(f);
          // Build Collection result
          Collection<D, std::tuple<K,Z>> result = Collection<D,std::tuple<K,Z>>(D<E>::getEngine());
          typename std::map<K,Z>::iterator it;
          for (it = accs.begin(); it != accs.end(); ++it) {
            std::tuple<K,Z> tup = std::make_tuple(it->first, it->second);
            result.insert(tup);
          }
         return result;
      }

      template <template <class> class F, class T>
      Collection<D, T> ext(std::function<Collection<F, T>(E)> expand) {
        Collection<D, T> result = Collection<D,T>(D<E>::getEngine());
        auto add_to_result = [&] (T elem) {result.insert(elem); };
        auto fun = [&] (E elem) {
          expand(elem).iterate(add_to_result);
        };
        D<E>::iterate(fun);
        return result;
      }

  private:
    friend class boost::serialization::access;
    // Serialize a collection by serializing its base-class (a dataspace)
    template<class Archive>
    void serialize(Archive &ar, const unsigned int version) {
      ar & boost::serialization::base_object<D<E>>(*this);
    }

  };

  template <typename E>
  // TODO: make this more generic? ie a SeqDS interface
  class Seq : public Collection<ListDS, E> {
    typedef Collection<ListDS, E> Super;
     public:
      Seq(Engine * e) : Super(e) {};

      Seq(const Seq<E>& other) : Super(other)  {}

      Seq(Super other) : Super(other) {}

      // Convert from Collection<ListDS, E> to Seq<E>
      std::tuple<Seq<E>, Seq<E>> split() {
        auto tup = Super::split();
        Super ds1 = get<0>(tup);
        Super ds2 = get<1>(tup);
        return std::make_tuple(Seq<E>(ds1), Seq<E>(ds2));
      }

      Seq<E> combine(const Seq<E>& other) {
       return Seq<E>(Super::combine(other));
      }

      template <class T>
      Seq<T> map(std::function<T(E)> f) {
       return Seq<T>(Super::map(f));
      }

      Seq<E> filter(std::function<bool(E)> f) {
       return Seq<E>(Super::filter(f));
      }

      Seq<E> sort(std::function<int(E,E)> f) {
        Super s = Super(ListDS<E>::sort(f));
        return Seq<E>(s);

      }

      template <class K, class Z>
      Seq<std::tuple<K, Z>> group_by 
      (std::function<K(E)> grouper, std::function<Z(Z, E)> folder, Z init) {
        Collection<ListDS, std::tuple<K,Z>> s = Super::group_by(grouper,folder,init);
        return Seq<std::tuple<K,Z>>(s);
      }

      template <class T>
      Seq<T> ext(std::function<Collection<ListDS, T>(E)> expand) {
        Collection<ListDS, T> result = Super::ext(expand);
        return Seq<T>(result);
      }
  };

  template <typename E>
  // TODO: make this more generic? ie a SetDS interface
  class Set : public Collection<SetDS, E> {
    typedef Collection<SetDS, E> Super;
    typedef SetDS<E> dataspace;
     public:
      Set(Engine * e) : Super(e) {};

      Set(const Set<E>& other) : Super(other)  {}

      Set(Super other) : Super(other) {}

      // Convert from Collection<ListDS, E> to Set<E>
      std::tuple<Set<E>, Set<E>> split() {
        auto tup = Super::split();
        Super ds1 = get<0>(tup);
        Super ds2 = get<1>(tup);
        return std::make_tuple(Set<E>(ds1), Set<E>(ds2));
      }

      Set<E> combine(const Set<E>& other) {
       return Set<E>(Super::combine(other));
      }

      template <class T>
      Set<T> map(std::function<T(E)> f) {
       return Set<T>(Super::map(f));
      }

      Set<E> filter(std::function<bool(E)> f) {
       return Set<E>(Super::filter(f));
      }

      template <class K, class Z>
      Set<std::tuple<K, Z>> group_by 
      (std::function<K(E)> grouper, std::function<Z(Z, E)> folder, Z init) {
        Collection<SetDS, std::tuple<K,Z>> s = Super::group_by(grouper,folder,init);
        return Set<std::tuple<K,Z>>(s);
      }

      template <class T>
      Set<T> ext(std::function<Collection<SetDS, T>(E)> expand) {
        Collection<SetDS, T> result = Super::ext(expand);
        return Set<T>(result);
      }

      bool member(E e) {
        return dataspace::member(e);
      }

      bool isSubsetOf(SetDS<E> other) {
        return dataspace::isSubsetOf(other);
      }

      // TODO union is a reserved word
      Set union1(Set<E> other) {
        Super s = Super(dataspace::union1(other));
        return Set<E>(s);
      }

      Set intersect(Set<E> other) {
        Super s = Super(dataspace::intersect(other));
        return Set<E>(s);
      }

      Set difference(Set<E> other) {
        Super s = Super(dataspace::difference(other));
        return Set<E>(s);
      }

  };

  template <typename E>
  class Sorted : public Collection<SortedDS, E> {
    typedef Collection<SortedDS, E> Super;
    typedef SortedDS<E> dataspace;
     public:
      Sorted(Engine * e) : Super(e) {};

      Sorted(const Sorted<E>& other) : Super(other)  {}

      Sorted(Super other) : Super(other) {}

      // Convert from Collection<ListDS, E> to Sorted<E>
      std::tuple<Sorted<E>, Sorted<E>> split() {
        auto tup = Super::split();
        Super ds1 = get<0>(tup);
        Super ds2 = get<1>(tup);
        return std::make_tuple(Sorted<E>(ds1), Sorted<E>(ds2));
      }

      Sorted<E> combine(const Sorted<E>& other) {
       return Sorted<E>(Super::combine(other));
      }

      template <class T>
      Sorted<T> map(std::function<T(E)> f) {
       return Sorted<T>(Super::map(f));
      }

      Sorted<E> filter(std::function<bool(E)> f) {
       return Sorted<E>(Super::filter(f));
      }

      template <class K, class Z>
      Sorted<std::tuple<K, Z>> group_by 
      (std::function<K(E)> grouper, std::function<Z(Z, E)> folder, Z init) {
        Collection<SortedDS, std::tuple<K,Z>> s = Super::group_by(grouper,folder,init);
        return Sorted<std::tuple<K,Z>>(s);
      }

      template <class T>
      Sorted<T> ext(std::function<Collection<SortedDS, T>(E)> expand) {
        Collection<SortedDS, T> result = Super::ext(expand);
        return Sorted<T>(result);
      }

      shared_ptr<E> min() { return dataspace::min(); }

      shared_ptr<E> max() { return dataspace::max(); }

      shared_ptr<E> lowerBound(E a) { return dataspace::lowerBound(a); }

      shared_ptr<E> upperBound(E a) { return dataspace::lowerBound(a); }

      Sorted<E> slice(E a, E b) {
        Super s = Super(dataspace::slice(a,b));
        return Sorted<E>(s);
      }

  };

  template <typename E>
  // TODO: make this more generic? ie an ExternalDS interface
  class ExternalCollection : public Collection<FileDS, E> {
    typedef Collection<FileDS, E> Super;
    typedef FileDS<E> Dataspace;
     public:
      ExternalCollection(Engine * e) : Super(e) {};

      ExternalCollection(const ExternalCollection<E>& other) : Super(other)  {}

      ExternalCollection(const Super& other) : Super(other) {}
      ExternalCollection(Super&& other) : Super(std::move(other)) {}

      // Convert from Collection<ListDS, E> to Set<E>
      std::tuple<Set<E>, Set<E>> split() {
        auto tup = Super::split();
        Super& ds1 = get<0>(tup);
        Super& ds2 = get<1>(tup);
        return std::make_tuple(ExternalCollection<E>(ds1), ExternalCollection<E>(ds2));
      }

      ExternalCollection<E> combine(const ExternalCollection<E>& other) {
       return ExternalCollection<E>(Super::combine(other));
      }

      template <class T>
      ExternalCollection<T> map(std::function<T(E)> f) {
       return ExternalCollection<T>(Super::map(f));
      }

      ExternalCollection<E> filter(std::function<bool(E)> f) {
       return ExternalCollection<E>(Super::filter(f));
      }

      template <class K, class Z>
      ExternalCollection<std::tuple<K, Z>> group_by 
            (std::function<K(E)> grouper, std::function<Z(Z, E)> folder, Z init) {
        Collection<FileDS, std::tuple<K,Z>> s = Super::group_by(grouper,folder,init);
        return ExternalCollection<std::tuple<K,Z>>(s);
      }

      template <class T>
      ExternalCollection<T> ext(std::function<Collection<SetDS, T>(E)> expand) {
        Collection<SetDS, T> result = Super::ext(expand);
        return ExternalCollection<T>(result);
      }
  };
}

#endif
