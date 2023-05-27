#pragma GCC optimize("Ofast")
#define _USE_MATH_DEFINES
#include <bits/stdc++.h>

#define ff first
#define ss second

#define typet typename T
#define typeu typename U
#define types typename... Ts
#define tempt template <typet>
#define tempu template <typeu>
#define temps template <types>
#define tandu template <typet, typeu>

#ifdef LOCAL
#include "debug.h"
#else
#define debug(...) \
  do {             \
  } while (false)
#endif  // LOCAL

using i64 = long long;
using u32 = unsigned int;
using u64 = unsigned long long;
using pii = std::pair<int, int>;
using vi = std::vector<int>;
using vl = std::vector<i64>;
using vs = std::vector<std::string>;
using vvi = std::vector<vi>;
using vp = std::vector<pii>;
tempt using heap = std::priority_queue<T, std::vector<T>, std::greater<T>>;

#define lowbit(x) ((x) & -(x))
#define range(x) std::begin(x), std::end(x)

tandu bool Min(T& x, const U& y) { return x > y ? x = y, true : false; }
tandu bool Max(T& x, const U& y) { return x < y ? x = y, true : false; }

// vs split(const std::string& s, const std::string& w = "\\s+") {
//   std::regex reg(w);
//   return vs(std::sregex_token_iterator(range(s), reg, -1), std::sregex_token_iterator());
// }


template <typet> struct double_type;
template <> struct double_type<u32> { using type = u64; };
template <> struct double_type<u64> { using type = __uint128_t; };
template <typet> using double_type_t = typename double_type<T>::type;


template <typet> struct Rabin;  // https://miller-rabin.appspot.com/
template <> struct Rabin<u32> { static constexpr u32 v[] = {2, 7, 61}; };
template <> struct Rabin<u64> {
  static constexpr u64 v[] = {2, 325, 9375, 28178, 450775, 9780504, 1795265022};
};

struct default_tag {};
struct no_tag {};

struct MillerBase {};
template <typet = default_tag> struct Miller;
template <> struct Miller<default_tag> : MillerBase {
  template <typet> static constexpr bool test(T p_) {
    using U = std::make_unsigned_t<T>;
    U& p = reinterpret_cast<U&>(p_);
    if (p < 32u) return 2693408940u >> p & 1;
    U q = p - 1;
    if (q % 6 & 3 or p % 5 == 0 or p % 7 == 0) return false;
    q /= 2;
    if (q < 60u) return true;
    for (double_type_t<U> a : Rabin<U>::v) {
      auto b = a % p;
      if (!b) continue;
      a = 1;
      for (U c = q / lowbit(q); c; c /= 2) {
        if (c & 1) a = a * b % p;
        b = b * b % p;
      }
      if (a == 1u) continue;
      for (int i = 0; a + 1 != p; ++i) {
        if (q >> i & 1) return false;
        a = a * a % p;
        if (a == 1u) return false;
      }
    }
    return true;
  }
};


// @return pair{g, x} s.t. g = gcd(a, m) and xa = g (mod m) and 0 <= x < m/g
constexpr std::pair<i64, i64> inv_gcd(i64 a, i64 m) {
  a %= m;
  if (a < 0) a += m;
  i64 x = 0, y = 1, b = m;
  while (a) {
    i64 t = b / a;
    b -= a * t;
    x -= y * t;
    t = a;
    a = b;
    b = t;
    t = x;
    x = y;
    y = t;
  }
  if (x < 0) x += m / b;
  return {b, x};
}

struct MintBase {};
struct StaticMintBase : MintBase {};
struct DynamicMintBase : MintBase {};

template <typet> struct is_mint : std::is_base_of<MintBase, T> {};
template <typet> struct is_static_mint : std::is_base_of<StaticMintBase, T> {};
template <typet> struct is_dynamic_mint : std::is_base_of<DynamicMintBase, T> {};
template <typet> constexpr bool is_mint_v = is_mint<T>::value;
template <typet> constexpr bool is_static_mint_v = is_static_mint<T>::value;
template <typet> constexpr bool is_dynamic_mint_v = is_dynamic_mint<T>::value;

template <u32 P> struct StaticMint : StaticMintBase {
  u32 v = 0;

  // reflection
  static constexpr bool is_prime() { return Miller<>::test(P); }
  using Mint = StaticMint;
  template <typet = int> static constexpr T mod() { return P; }
  template <typet = int> constexpr T val() const { return v; }
  template <typet = int> constexpr operator T() const { return v; }

  // constructor
  constexpr StaticMint() = default;
  template <typet> constexpr StaticMint(T x) : v(x % mod()) {
    if constexpr (std::is_signed_v<T>) {
      if (v >> 31) v += P;
    }
  }

  // io
  friend std::istream& operator>>(std::istream& is, Mint& x) {
    i64 y;
    is >> y;
    x = y;
    return is;
  }
  friend std::ostream& operator<<(std::ostream& os, Mint x) { return os << x.v; }

  // comparision
  friend constexpr bool operator==(Mint lhs, Mint rhs) { return lhs.v == rhs.v; }
  friend constexpr bool operator!=(Mint lhs, Mint rhs) { return lhs.v != rhs.v; }
  friend constexpr bool operator<(Mint lhs, Mint rhs) { return lhs.v < rhs.v; }
  friend constexpr bool operator<=(Mint lhs, Mint rhs) { return lhs.v <= rhs.v; }
  friend constexpr bool operator>(Mint lhs, Mint rhs) { return lhs.v > rhs.v; }
  friend constexpr bool operator>=(Mint lhs, Mint rhs) { return lhs.v >= rhs.v; }

  // arithmetic
  constexpr Mint& operator+=(Mint rhs) {
    v += rhs.v;
    if (v >= P) v -= P;
    return *this;
  }
  constexpr Mint& operator-=(Mint rhs) {
    v -= rhs.v;
    if (v >= P) v += P;
    return *this;
  }
  constexpr Mint& operator*=(Mint rhs) {
    v = static_cast<u64>(v) * rhs.v % P;
    return *this;
  }
  constexpr Mint& operator/=(Mint rhs) { return *this *= ~rhs; }
  template <typet> constexpr Mint& operator^=(T rhs) {
    Mint u = *this;
    v = 1;
    for (u32 n = (rhs % static_cast<int>(P - 1) + P - 1) % (P - 1); n; n /= 2) {
      if (n & 1) *this *= u;
      u *= u;
    }
    return *this;
  }
  friend constexpr Mint operator+(Mint lhs, Mint rhs) { return lhs += rhs; }
  friend constexpr Mint operator-(Mint lhs, Mint rhs) { return lhs -= rhs; }
  friend constexpr Mint operator*(Mint lhs, Mint rhs) { return lhs *= rhs; }
  friend constexpr Mint operator/(Mint lhs, Mint rhs) { return lhs /= rhs; }
  template <typet> friend constexpr Mint operator^(Mint lhs, T rhs) { return lhs ^= rhs; }
  constexpr Mint operator+() const { return *this; }
  constexpr Mint operator-() const { return Mint{} - *this; }
  constexpr Mint operator~() const {
    if constexpr (is_prime()) {
      return *this ^ (P - 2);
    } else {
      auto [g, x] = inv_gcd(v, P);
      assert(g == 1);
      return x;
    }
  }
};
template <u32 P> using Fp = std::enable_if_t<StaticMint<P>::is_prime(), StaticMint<P>>;

constexpr u32 get_ntt_proot(u32 p) {
  assert(Miller<>::test(p));
  if (p == 2u) return 1;
  if (p == 998244353u) return 3;
  for (u32 g = 2; g < p; g++) {
    u64 u = g, v = 1;
    for (u32 m = p / 2; m; m /= 2) {
      if (m & 1) v = v * u % p;
      u = u * u % p;
    }
    if (v != 1) return g;
  }
  return -1;
}

template <typet> void butterfly(T* a, int n) {
  int* rev = new int[n];
  rev[0] = 0;
  for (int i = 0; i < n; i++) {
    rev[i] = rev[i / 2] / 2;
    if (i & 1) rev[i] |= n / 2;
  }
  for (int i = 0; i < n; i++)
    if (i < rev[i]) std::swap(a[i], a[rev[i]]);
  delete[] rev;
}


template <typet> struct is_complex : std::false_type {};
template <typet> struct is_complex<std::complex<T>> : std::true_type {};
template <typet> constexpr bool is_complex_v = is_complex<T>::value;

template <typet> std::vector<T> fft_root = {0, 1};
template <typet> T get_fft_root(int n) {
  static_assert(is_static_mint_v<T>);
  assert((T::mod() - 1) % n == 0);
  return T{get_ntt_proot(T::mod())} ^ (T::mod() - 1) / n;
}
std::complex<long double> get_fft_root(int n, int i) {
  return std::polar<long double>(1, std::acos(-1.l) * 2 / n * i);
}
template <typet> void reserve_fft_roots(int n) {
  assert(n == lowbit(n));
  auto& wn = fft_root<T>;
  int m = wn.size();
  if (n <= m) return;
  wn.resize(n);
  if constexpr (is_static_mint_v<T>) {
    T r = get_fft_root<T>(n);
    wn[n / 2] = 1;
    for (int i = n / 2 + 1; i < n; i++) wn[i] = wn[i - 1] * r;
  } else if constexpr (is_complex_v<T>) {
    for (int i = 0; i < n / 2; i++) wn[n / 2 + i] = get_fft_root(n, i);
  } else {
    []<bool flag = false>() { static_assert(flag, "invalid fft type"); }
    ();
  }
  for (int i = n / 2 - 1; i >= m; i--) wn[i] = wn[i * 2];
}

template <typet> void dft(T* a, int n) {
  if (n == 1) return;
  if (n == 2) {
    a[0] += a[1];
    a[1] = a[0] - a[1] - a[1];
    return;
  }
  reserve_fft_roots<T>(n);
  butterfly(a, n);
  for (int i = 1; i < n; i *= 2) {
    const T* w = fft_root<T>.data() + i;
    for (T* b = a; b != a + n; b += i) {
      for (int j = 0; j < i; j++) {
        T t = b[i] * w[j];
        b[i] = *b - t;
        *b++ += t;
      }
    }
  }
}
template <typet> void idft(T* a, int n) {
  std::reverse(a + 1, a + n);
  dft(a, n);
  for (int i = 0; i < n; i++) {
    if constexpr (is_static_mint_v<T>) {
      a[i] *= T::mod() - (T::mod() - 1) / n;
    } else if constexpr (is_complex_v<T>) {
      a[i] *= static_cast<typename T::value_type>(1) / n;
    }
  }
}

// g is after dft
template <typet> void cycle_conv_xxx(T* f, const T* g, int n) {
  dft(f, n);
  for (int i = 0; i < n; i++) f[i] *= g[i];
  idft(f, n);
}
// f <- f * g % (x^n - 1)
template <typet> void cycle_conv(T* f, T* g, int n) {
  dft(g, n);
  cycle_conv_xxx(f, g, n);
}


struct fft_tag {};
struct ntt_tag {};
struct mtt_tag {};
struct default_conj_tag {};
struct mtt_conj_tag {};

template <typet> struct make_conj { using type = T; };
template <> struct make_conj<default_tag> { using type = default_conj_tag; };
template <> struct make_conj<mtt_tag> { using type = mtt_conj_tag; };
template <typet> using make_conj_t = typename make_conj<T>::type;

template <typet, typename = void> struct poly_tag_for;
template <typet> struct poly_tag_for<T, std::enable_if_t<is_static_mint_v<T>>> {
  static constexpr int N = T::mod();
  using type = std::conditional_t<T::is_prime() and (N - 1) % (1 << 20) == 0, ntt_tag,
                                  std::conditional_t<(N < 10000), default_tag, mtt_tag>>;
};
template <typet> struct poly_tag_for<T, std::enable_if_t<is_dynamic_mint_v<T>>> {
  using type = mtt_tag;
};
template <typet> struct poly_tag_for<T, std::enable_if_t<is_complex_v<T>>> {
  using type = fft_tag;
};
template <typet> struct poly_tag_for<T, std::enable_if_t<std::is_arithmetic_v<T>>> {
  using type = default_tag;
};
template <typet> using poly_tag_for_t = typename poly_tag_for<T>::type;


template <typet, typename = typename poly_tag_for<T>::type> struct Poly {};
template <typet> using PolyConj = Poly<T, make_conj_t<poly_tag_for_t<T>>>;

template <typet> struct PolyBase : std::vector<T> {
  using type = std::vector<T>;
  using type::type;
  PolyBase(type other) : type(std::move(other)) {}
  template <typeu> PolyBase(const std::vector<U>& other) : type(range(other)) {}
  void fix() {
    for (; !type::empty(); type::pop_back()) {
      if constexpr (is_static_mint_v<T>) {
        if (type::back()) break;
      } else {
        if (std::abs(type::back()) > 1e-9) break;
      }
    }
    if (type::empty()) type::resize(1);
  }
  PolyBase& operator+=(const PolyBase& rhs) {
    type::resize(std::max(type::size(), rhs.size()));
    for (int i = 0; i < static_cast<int>(rhs.size()); i++) (*this)[i] += rhs[i];
    fix();
    return *this;
  }
  PolyBase& operator-=(const PolyBase& rhs) {
    type::resize(std::max(type::size(), rhs.size()));
    for (int i = 0; i < static_cast<int>(rhs.size()); i++) (*this)[i] -= rhs[i];
    fix();
    return *this;
  }
  PolyBase& operator*=(T rhs) {
    for (T& lhs : *this) lhs *= rhs;
    fix();
    return *this;
  }
  PolyBase& operator/=(T rhs) {
    for (T& lhs : *this) lhs /= rhs;
    fix();
    return *this;
  }
  bool brute_mul_(PolyBase& rhs) {
    fix();
    rhs.fix();
#ifdef LOCAL
    return false;
#endif  // LOCAL
    int n = type::size(), m = rhs.size();
    if (n + m > 50 and std::min(n, m) > 32 - __builtin_clz(n + m)) return false;
    type lhs(n + m - 1);
    type::swap(lhs);
    for (int i = 0; i < n; i++)
      for (int j = 0; j < m; j++) (*this)[i + j] += lhs[i] * rhs[j];
    fix();
    return true;
  }
  PolyBase& operator*=(PolyBase rhs) {
    if (!brute_mul_(rhs)) {
      int n = 1 << (32 - __builtin_clz(type::size() + rhs.size() - 2));
      type::resize(n);
      rhs.resize(n);
      cycle_conv(type::data(), rhs.data(), n);
      fix();
    }
    return *this;
  }
  friend PolyBase operator+(PolyBase lhs, const PolyBase& rhs) { return lhs += rhs; }
  friend PolyBase operator-(PolyBase lhs, const PolyBase& rhs) { return lhs -= rhs; }
  friend PolyBase operator*(PolyBase lhs, T rhs) { return lhs *= rhs; }
  friend PolyBase operator*(T lhs, PolyBase rhs) { return rhs *= lhs; }
  friend PolyBase operator/(PolyBase lhs, T rhs) { return lhs /= rhs; }
  friend PolyBase operator*(PolyBase lhs, PolyBase rhs) { return lhs *= std::move(rhs); }
  template <typeu = std::complex<double>> PolyBase<U> dft_conj(int n) {
    using dt = typename U::value_type;
    PolyBase<U> f(n);
    std::copy(range(*this), reinterpret_cast<dt*>(f.data()));
    if (n == 1) return f;
    reserve_fft_roots<U>(n);
    dft(f.data(), n / 2);
    for (int i = 0; i <= n / 4; i++) {
      int j = (n / 2 - i) & (n / 2 - 1);
      U u = (f[i] + std::conj(f[j])) * static_cast<dt>(0.5),
        v = (std::conj(f[j]) - f[i]) * fft_root<U>[n / 2 + i] * U(0, 0.5);
      f[i] = u + v;
      f[n / 2 + i] = u - v;
      if (i != j) {
        f[j] = std::conj(f[n / 2 + i]);
        f[n / 2 + j] = std::conj(f[i]);
      }
    }
    return f;
  }
  template <typeu> void idft_conj(PolyBase<U> f) {
    using dt = typename U::value_type;
    int n = f.size();
    reserve_fft_roots<U>(n);
    for (int i = 0, j = n / 2; i < n / 2; i++, j++)
      f[i] = (f[i] + f[j] + (f[i] - f[j]) * std::conj(fft_root<U>[j]) * U(0, 1)) *
             static_cast<dt>(0.5);
    idft(f.data(), n / 2);
    dt* g = reinterpret_cast<dt*>(f.data());
    type::resize(n);
    for (int i = 0; i < n; i++) {
      if constexpr (std::is_floating_point_v<T>) {
        (*this)[i] = g[i];
      } else {
        (*this)[i] = std::llround(g[i]);
      }
    }
  }
};

#define POLY_HEAD              \
  using type = std::vector<T>; \
  using PolyBase<T>::PolyBase; \
  using PolyBase<T>::fix;      \
  using PolyBase<T>::brute_mul_

template <typet> struct Poly<T, default_tag> : PolyBase<T> {
  POLY_HEAD;
  using PolyComplex =
      PolyBase<std::complex<std::conditional_t<std::is_floating_point_v<T>, T, double>>>;
  Poly(const PolyComplex& other) : PolyBase<T>(other.size()) {
    for (int i = 0; i < static_cast<int>(type::size()); i++) {
      if constexpr (std::is_floating_point_v<T>) {
        (*this)[i] = other[i].real();
      } else {
        (*this)[i] = std::llround(other[i].real());
      }
    }
  }
  friend Poly operator*(const Poly& lhs, const Poly& rhs) {
    return PolyComplex(lhs) * PolyComplex(rhs);
  }
  Poly& operator*=(const Poly& rhs) { return *this = *this * rhs; }
};

template <typet> struct Poly<T, fft_tag> : PolyBase<T> {
  POLY_HEAD;

  Poly& shrink(int n) {
    if (static_cast<int>(type::size()) > n) type::resize(n);
    fix();
    return *this;
  }
  friend Poly head(const Poly& f, int n) {
    Poly g(f.begin(), f.begin() + std::min<int>(f.size(), n));
    g.fix();
    return g;
  }
  friend Poly head(Poly&& f, int n) {
    if (static_cast<int>(f.size()) > n) f.resize(n);
    f.fix();
    return f;
  }

  Poly square() {
    fix();
    if (type::size() < 50) return *this * *this;
    int n = 1 << (33 - __builtin_clz(type::size() - 1));
    Poly f(n);
    std::copy(range(*this), f.begin());
    dft(f.data(), n);
    for (int i = 0; i < n; i++) f[i] *= f[i];
    idft(f.data(), n);
    return f;
  }

  Poly inv(int m = -1) {
    fix();
    if (m == -1) m = type::size();
    Poly f{T(1) / (*this)[0]};
    for (int k = 2; k < m * 2; k *= 2) f = f * 2 - Poly(f.square() * head(*this, k)).shrink(k);
    f.resize(m);
    return f;
  }
};

template <typet> struct Poly<T, ntt_tag> : PolyBase<T> {
  POLY_HEAD;

  // 10nlogn
  static void inv_impl(const T* f, T* g, int n) {
    assert(n == lowbit(n));
    int m = std::min(n, 16);
    std::fill_n(g, m, 0);
    g[0] = T(1) / f[0];
    for (int i = 1; i < m; i++) {
      for (int j = 0; j < i; j++) g[i] -= f[i - j] * g[j];
      g[i] *= g[0];
    }
    T* a = new T[n * 2];
    for (; m < n; m *= 2) {
      std::copy_n(f, m * 2, a);
      std::copy_n(g, m, a + n);
      std::fill_n(a + n + m, m, 0);
      cycle_conv(a, a + n, m * 2);
      std::fill_n(a, m, 0);
      cycle_conv_xxx(a, a + n, m * 2);
      for (int i = m; i < m * 2; i++) g[i] = -a[i];
    }
    delete[] a;
  }
  Poly inv(int m = -1) {
    fix();
    int n = type::size();
    if (m == -1) m = n;
    if (n > 2) n = 1 << (32 - __builtin_clz(n - 1));
    type::resize(n);
    Poly g(n);
    inv_impl(type::data(), g.data(), n);
    g.resize(m);
    return g;
  }
};

template <typet> struct Poly<T, mtt_tag> : PolyBase<T> {
  POLY_HEAD;
  Poly& operator*=(Poly rhs) {
    if (!brute_mul_(rhs)) {
      int n = 1 << (32 - __builtin_clz(type::size() + rhs.size() - 2)), s = std::sqrt(T::mod());
      PolyBase<std::complex<double>> f[5];
      for (int j = 0; j < 5; j++) f[j].resize(n);
      for (int i = 0; i < static_cast<int>(type::size()); i++) f[0][i] = (*this)[i].val() % s;
      for (int i = 0; i < static_cast<int>(type::size()); i++) f[1][i] = (*this)[i].val() / s;
      for (int i = 0; i < static_cast<int>(rhs.size()); i++) f[3][i] = rhs[i].val() % s;
      for (int i = 0; i < static_cast<int>(rhs.size()); i++) f[4][i] = rhs[i].val() / s;
      for (int j : {0, 1, 3, 4}) dft(f[j].data(), n);
      std::copy(range(f[1]), f[2].begin());
      for (int i = 0; i < n; i++) {
        f[2][i] *= f[4][i];
        f[1][i] *= f[3][i];
        f[1][i] += f[0][i] * f[4][i];
        f[0][i] *= f[3][i];
      }
      type::resize(0);
      type::resize(n);
      for (int j = 0; j < 3; j++) {
        idft(f[j].data(), n);
        T t = 1;
        for (int i = 0; i < j; i++) t *= s;
        for (int i = 0; i < n; i++) (*this)[i] += t * std::llround(f[j][i].real());
      }
    }
    fix();
    return *this;
  }
  friend Poly operator*(Poly lhs, Poly rhs) { return lhs *= std::move(rhs); }
};

template <typet> struct Poly<T, default_conj_tag> : PolyBase<T> {
  POLY_HEAD;
  using complex = std::complex<std::conditional_t<std::is_floating_point_v<T>, T, double>>;
  Poly& operator*=(Poly rhs) {
    if (!brute_mul_(rhs)) {
      int n = 1 << (32 - __builtin_clz(type::size() + rhs.size() - 2));
      auto f = PolyBase<T>::dft_conj(n);
      auto g = rhs.dft_conj(n);
      for (int i = 0; i < n; i++) f[i] *= g[i];
      PolyBase<T>::idft_conj(std::move(f));
    }
    fix();
    return *this;
  }
  friend Poly operator*(Poly lhs, Poly rhs) { return lhs *= std::move(rhs); }
};

template <typet> struct Poly<T, mtt_conj_tag> : PolyBase<T> {
  POLY_HEAD;
  Poly& operator*=(Poly rhs) {
    if (!brute_mul_(rhs)) {
      int n = 1 << (32 - __builtin_clz(type::size() + rhs.size() - 2)), s = std::sqrt(T::mod());
      PolyBase<std::complex<double>> f[5];
      PolyBase<T> aux(type::size());
      for (int i = 0; i < static_cast<int>(type::size()); i++) aux[i] = (*this)[i].val() % s;
      f[0] = aux.dft_conj(n);
      for (int i = 0; i < static_cast<int>(type::size()); i++) aux[i] = (*this)[i].val() / s;
      f[1] = f[2] = aux.dft_conj(n);
      aux.resize(rhs.size());
      for (int i = 0; i < static_cast<int>(rhs.size()); i++) aux[i] = rhs[i].val() % s;
      f[3] = aux.dft_conj(n);
      for (int i = 0; i < static_cast<int>(rhs.size()); i++) aux[i] = rhs[i].val() / s;
      f[4] = aux.dft_conj(n);
      for (int i = 0; i < n; i++) {
        f[2][i] *= f[4][i];
        f[1][i] *= f[3][i];
        f[1][i] += f[0][i] * f[4][i];
        f[0][i] *= f[3][i];
      }
      type::clear();
      type::resize(n);
      for (int j = 0; j < 3; j++) {
        aux.idft_conj(f[j]);
        T t = 1;
        for (int i = 0; i < j; i++) t *= s;
        for (int i = 0; i < n; i++) (*this)[i] += t * aux[i];
      }
    }
    fix();
    return *this;
  }
  friend Poly operator*(Poly lhs, Poly rhs) { return lhs *= std::move(rhs); }
};

template <typet> void dft_v2(T* a, int n) {
  if (n == 1) return;
  if (n == 2) {
    a[0] += a[1];
    a[1] = a[0] - a[1] - a[1];
    return;
  }
  reserve_fft_roots<T>(n);
  butterfly(a, n);
  for (T* b = a; b != a + n; b += 2) {
    b[0] += b[1];
    b[1] = b[0] - b[1] - b[1];
  }
  for (T* b = a; b != a + n; b += 4) {
    b[0] += b[2];
    b[2] = b[0] - b[2] - b[2];
    T t = b[3] * fft_root<T>[3];
    b[3] = b[1] - t;
    b[1] += t;
  }
  for (int i = 4; i < n; i *= 2) {
    const T* w = fft_root<T>.data() + i;
    for (T* b = a; b != a + n; b += i + 1) {
      b[0] += b[i];
      b[i] = b[0] - b[i] - b[i];
      for (int j = 1; j < i; j++) {
        T t = (++b)[i] * w[j];
        b[i] = b[0] - t;
        b[0] += t;
      }
    }
  }
}
template <typet> void idft_v2(T* a, int n) {
  std::reverse(a + 1, a + n);
  dft_v2(a, n);
  for (int i = 0; i < n; i++) {
    if constexpr (is_static_mint_v<T>) {
      a[i] *= T::mod() - (T::mod() - 1) / n;
    } else if constexpr (is_complex_v<T>) {
      a[i] *= static_cast<typename T::value_type>(1) / n;
    }
  }
}
struct mtt_conj_v2tag {};
template <typet, typename = void> struct poly_v2tag_for { using type = poly_tag_for_t<T>; };
template <typet>
struct poly_v2tag_for<T, std::enable_if_t<std::is_same_v<poly_tag_for_t<T>, mtt_tag>>> {
  using type = mtt_conj_v2tag;
};
template <typet> using poly_v2tag_for_t = typename poly_v2tag_for<T>::type;
template <typet> using PolyV2 = Poly<T, make_conj_t<poly_v2tag_for_t<T>>>;
template <typet> struct Poly<T, mtt_conj_v2tag> : PolyBase<T> {
  POLY_HEAD;
  using complex = std::complex<double>;
  Poly& operator*=(Poly rhs) {
    if (!brute_mul_(rhs)) {
      int n = 1 << (32 - __builtin_clz(type::size() + rhs.size() - 2)), s = std::sqrt(T::mod());
      PolyBase<complex> f(n), g(n);
      for (int i = 0; i < static_cast<int>(type::size()); i++)
        f[i] = complex((*this)[i].val() % s, (*this)[i].val() / s);
      for (int i = 0; i < static_cast<int>(rhs.size()); i++)
        g[i] = complex(rhs[i].val() % s, rhs[i].val() / s);
      dft_v2(f.data(), n);
      dft_v2(g.data(), n);
      for (int i = 0; i <= n / 2; i++) {
        int j = (n - i) & (n - 1);
        complex t[4] = {(f[i] + std::conj(f[j])) * 0.5, (std::conj(f[j]) - f[i]) * complex(0, 0.5),
                        (g[i] + std::conj(g[j])) * 0.5, (std::conj(g[j]) - g[i]) * complex(0, 0.5)};
        g[i] = t[0] * t[3] + t[1] * t[2];
        t[0] *= t[2];
        t[1] *= t[3] * complex(0, 1);
        f[i] = t[0] + t[1];
        if (i != j) {
          f[j] = std::conj(t[0] - t[1]);
          g[j] = std::conj(g[i]);
        }
      }
      for (int i = 0, j = n / 2; i < n / 2; i++, j++)
        g[i] =
            (g[i] + g[j] + (g[i] - g[j]) * std::conj(fft_root<complex>[j]) * complex(0, 1)) * 0.5;
      idft_v2(f.data(), n);
      idft_v2(g.data(), n / 2);
      type::resize(n);
      for (int i = 0; i < n; i++) {
        T t[3] = {std::llround(f[i].real()), std::llround(reinterpret_cast<double*>(g.data())[i]),
                  std::llround(f[i].imag())};
        (*this)[i] = t[0] + (t[1] + t[2] * s) * s;
      }
    }
    fix();
    return *this;
  }
  friend Poly operator*(Poly lhs, Poly rhs) { return lhs *= std::move(rhs); }
};

#undef POLY_HEAD


template <typet> T product(const std::vector<T>& F) {
  struct Comp {
    bool operator()(const T& lhs, const T& rhs) const { return lhs.size() > rhs.size(); }
  };
  std::priority_queue<T, std::vector<T>, Comp> heap;
  for (const T& f : F) heap.push(f);
  T f = heap.top();
  heap.pop();
  while (!heap.empty()) {
    T g = heap.top();
    heap.pop();
    f *= g;
    heap.push(std::move(f));
    f = heap.top();
    heap.pop();
  }
  return f;
}


using Z = Fp<998244353>;

void initialize() {
  std::cin.tie(nullptr)->sync_with_stdio(false);
  std::cout << std::fixed << std::setprecision(10);
}


int cas;

void solution() {
  int n;
  std::cin >> n;
  Poly<Z, fft_tag> f(n);
  // Poly<Z> f(n);
  for (int i = 0; i < n; i++) {
    std::cin >> f[i];
  }
  f = f.inv();
  for (int i = 0; i < n; i++) {
    std::cout << f[i] << " \n"[i == n - 1];
  }
}


int main() {
  initialize();
  int T = 1;
  // std::cin >> T;
  for (cas = 1; cas <= T; cas++) solution();
  return 0;
}
