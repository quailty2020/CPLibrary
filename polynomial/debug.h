#include <bitset>
#include <iostream>
#include <iterator>
#include <queue>
#include <string>
#include <string_view>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>


#define __UNPACK_IMPL__(...) __VA_ARGS__
#define __UNPACK__(PACK) __UNPACK_IMPL__ PACK

#define __ARG1__(_1, ...) _1
#define __ARG2__(_1, _2, ...) _2
#define __ARG3__(_1, _2, _3, ...) _3
#define __ARG4__(_1, _2, _3, _4, ...) _4
#define __ARG64__(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, \
                  _19, _20, _21, _22, _23, _24, _25, _26, _27, _28, _29, _30, _31, _32, _33, _34,  \
                  _35, _36, _37, _38, _39, _40, _41, _42, _43, _44, _45, _46, _47, _48, _49, _50,  \
                  _51, _52, _53, _54, _55, _56, _57, _58, _59, _60, _61, _62, _63, _64, ...)       \
  _64

#define __RESQ64__                                                                                \
  63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, \
      39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, \
      16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0

#define __NARG_IMPL__(...) __ARG64__(__VA_ARGS__)
#define __NARG__(...) __NARG_IMPL__(__VA_ARGS__, __RESQ64__)

#define FOO_NAME_ARY(NAME, N) NAME##_##N##ARY
#define FOO_NAME(NAME, N) FOO_NAME_ARY(NAME, N)
/** Use
 *  #define FOO(...) FOO_NAME(FOO, __NARG__(__VA_ARGS__))(__VA_ARGS__)
 *  to define variable number of arguments.
 */


#define DECLARE_V_HELPER(...) FOO_NAME(DECLARE_V_HELPER, __NARG__(__VA_ARGS__))(__VA_ARGS__)
#define DECLARE_V_HELPER_1ARY(NAME) DECLARE_V_HELPER_3ARY(NAME, (typename T), (T))
#define DECLARE_V_HELPER_3ARY(NAME, PACK1, PACK2) \
  template <__UNPACK__(PACK1)>                    \
  constexpr typename NAME<__UNPACK__(PACK2)>::value_type NAME##_v = NAME<__UNPACK__(PACK2)>::value


template <typename T, typename... Ts>
struct is_one_of : std::disjunction<std::is_same<T, Ts>...> {};
DECLARE_V_HELPER(is_one_of, (typename T, typename... Ts), (T, Ts...));


template <typename T, template <typename...> class Template>
struct is_specialization_of : std::false_type {};
template <template <typename...> class Template, typename... Ts>
struct is_specialization_of<Template<Ts...>, Template> : std::true_type {};
DECLARE_V_HELPER(is_specialization_of, (typename T, template <typename...> class Template),
                 (T, Template));


#define DECLARE_IS_SPEC(...) FOO_NAME(DECLARE_IS_SPEC, __NARG__(__VA_ARGS__))(__VA_ARGS__)
#define DECLARE_IS_SPEC_1ARY(NAME) DECLARE_SPEC_TRAITS(is_##NAME, NAME)
#define DECLARE_IS_SPEC_2ARY(FIELD, NAME) DECLARE_SPEC_TRAITS(is_##NAME, FIELD::NAME)
#define DECLARE_SPEC_TRAITS(SPEC, TEMP)                                 \
  template <typename T> struct SPEC : is_specialization_of<T, TEMP> {}; \
  DECLARE_V_HELPER(SPEC)

DECLARE_IS_SPEC(std, pair);
DECLARE_IS_SPEC(std, tuple);
DECLARE_IS_SPEC(std, queue);
DECLARE_IS_SPEC(std, priority_queue);


template <typename T> using begin_type = decltype(std::begin(std::declval<T>()));
template <typename, typename = void> struct has_begin_helper : std::false_type {};
template <typename T> struct has_begin_helper<T, std::void_t<begin_type<T>>> : std::true_type {};
template <typename T> using has_begin = has_begin_helper<T>;
DECLARE_V_HELPER(has_begin);


template <typename T>
struct is_rai : std::is_same<typename std::iterator_traits<T>::iterator_category,
                             std::random_access_iterator_tag> {};
DECLARE_V_HELPER(is_rai);


constexpr std::string_view c_escape(const char& c) {
  if (c == '\0') {
    return "\\0";
  } else if (c == '\a') {
    return "\\a";
  } else if (c == '\b') {
    return "\\b";
  } else if (c == '\t') {
    return "\\t";
  } else if (c == '\n') {
    return "\\n";
  } else if (c == '\v') {
    return "\\v";
  } else if (c == '\f') {
    return "\\f";
  } else if (c == '\r') {
    return "\\r";
  } else if (c == '\e') {
    return "\\e";
  } else if (c == '\'') {
    return "\\\'";
  } else if (c == '\"') {
    return "\\\"";
  } else if (c == '\\') {
    return "\\\\";
  } else {
    return std::string_view(&c, 1);
  }
}


template <typename T> void print_impl(std::ostream&, T&& x);
template <typename Tuple, std::size_t... Is>
void print_tuple_impl(std::ostream& os, Tuple&& t, std::index_sequence<Is...>);

template <typename T> void print_impl(std::ostream& os, T&& x) {
  using U = std::decay_t<T>;
  if constexpr (is_one_of_v<U, bool>) {
    os << (x ? "True" : "False");
  } else if constexpr (is_one_of_v<U, signed char>) {
    os << static_cast<short>(x);
  } else if constexpr (is_one_of_v<U, unsigned char>) {
    os << static_cast<unsigned short>(x);
  } else if constexpr (is_one_of_v<U, char>) {
    os << '\'' << c_escape(x) << '\'';
  } else if constexpr (is_one_of_v<U, char*, const char*>) {
    os << '\"';
    for (const char* ptr = x; *ptr; ptr++) os << c_escape(*ptr);
    os << '\"';
  } else if constexpr (is_one_of_v<U, std::string, std::string_view>) {
    os << '\"';
    for (const char& c : x) os << c_escape(c);
    os << '\"';
  } else if constexpr (is_one_of_v<U, std::vector<bool>>) {
    for (auto&& b : x) os << b;
  } else if constexpr (is_pair_v<U>) {
    print_impl(os << '<', std::forward<T>(x).first);
    print_impl(os << ',', std::forward<T>(x).second);
    os << '>';
  } else if constexpr (is_tuple_v<U>) {
    print_tuple_impl(os, std::forward<T>(x), std::make_index_sequence<std::tuple_size_v<U>>{});
  } else if constexpr (has_begin_v<T>) {
    using Iterator = begin_type<T>;
    constexpr bool flag = is_rai_v<Iterator>;
    Iterator it = std::begin(x), ed = std::end(x);
    os << (flag ? '[' : '{');
    if (it != ed) {
      print_impl(os, *it++);
      while (it != ed) print_impl(os << ',', *it++);
    }
    os << (flag ? ']' : '}');
  } else if constexpr (is_queue_v<U>) {
    U a(x);
    std::vector<typename U::value_type> b;
    for (; !a.empty(); a.pop()) b.push_back(a.front());
    print_impl(os, b);
  } else if constexpr (is_priority_queue_v<U>) {
    U a(x);
    std::vector<typename U::value_type> b;
    for (; !a.empty(); a.pop()) b.push_back(a.top());
    print_impl(os, b);
  } else {
    os << x;
  }
}

template <typename Tuple, std::size_t... Is>
void print_tuple_impl(std::ostream& os, Tuple&& t, std::index_sequence<Is...>) {
  (print_impl(os << (Is ? ',' : '<'), std::get<Is>(std::forward<Tuple>(t))), ...);
  os << '>';
}


namespace dbg {

std::ostream* debug_stream_ptr = &std::cerr;
void set_debug_stream(std::ostream& os) { debug_stream_ptr = &os; }

}  // namespace dbg

using dbg::set_debug_stream;

template <typename... Ts> void debug_impl(Ts&&... args) {
  (..., print_impl(*dbg::debug_stream_ptr << ' ', std::forward<Ts>(args)));
  *dbg::debug_stream_ptr << std::endl;
}

#define debug(...) *dbg::debug_stream_ptr << "[" #__VA_ARGS__ "] :", debug_impl(__VA_ARGS__)


#undef __UNPACK_IMPL__
#undef __UNPACK__
#undef __ARG1__
#undef __ARG2__
#undef __ARG3__
#undef __ARG4__
#undef __ARG64__
#undef __RESQ64__
#undef __NARG_IMPL__
#undef __NARG__
#undef FOO_NAME_ARY
#undef FOO_NAME
#undef DECLARE_V_HELPER
#undef DECLARE_V_HELPER_1ARY
#undef DECLARE_V_HELPER_3ARY
#undef DECLARE_IS_SPEC
#undef DECLARE_IS_SPEC_1ARY
#undef DECLARE_IS_SPEC_2ARY
#undef DECLARE_SPEC_TRAITS
