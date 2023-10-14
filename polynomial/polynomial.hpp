#ifndef CPLIBRARY_POLYNOMIAL_HPP
#define CPLIBRARY_POLYNOMIAL_HPP

namespace math {

template<typename T>
constexpr T power(T a, long long b) {
    T res = 1;
    while (b) {
        if (b & 1) res *= a;
        if (b > 1) a *= a;
        b >>= 1;
    }
    return res;
}

constexpr long long safe_mod(long long x, long long m) {
    x %= m;
    if (x < 0) x += m;
    return x;
}

constexpr long long pow_mod_constexpr(long long x, long long n, int m) {
    if (m == 1) return 0;
    unsigned int _m = (unsigned int)(m);
    unsigned long long r = 1;
    unsigned long long y = safe_mod(x, m);
    while (n) {
        if (n & 1) r = (r * y) % _m;
        if (n > 1) y = (y * y) % _m;
        n >>= 1;
    }
    return r;
}

constexpr bool is_prime_constexpr(int n) {
    if (n <= 1) return false;
    if (n == 2 || n == 7 || n == 61) return true;
    if (n % 2 == 0) return false;
    long long d = n - 1;
    while (d % 2 == 0) d /= 2;
    constexpr long long bases[3] = {2, 7, 61};
    for (long long a : bases) {
        long long t = d;
        long long y = pow_mod_constexpr(a, t, n);
        while (t != n - 1 && y != 1 && y != n - 1) {
            y = y * y % n;
            t <<= 1;
        }
        if (y != n - 1 && t % 2 == 0) {
            return false;
        }
    }
    return true;
}

constexpr int primitive_root_constexpr(int m) {
    if (m == 2) return 1;
    if (m == 167772161) return 3;
    if (m == 469762049) return 3;
    if (m == 754974721) return 11;
    if (m == 998244353) return 3;
    int divs[20] = {};
    divs[0] = 2;
    int cnt = 1;
    int x = (m - 1) / 2;
    while (x % 2 == 0) x /= 2;
    for (int i = 3; (long long)(i)*i <= x; i += 2) {
        if (x % i == 0) {
            divs[cnt++] = i;
            while (x % i == 0) {
                x /= i;
            }
        }
    }
    if (x > 1) {
        divs[cnt++] = x;
    }
    for (int g = 2;; g++) {
        bool ok = true;
        for (int i = 0; i < cnt; i++) {
            if (pow_mod_constexpr(g, (m - 1) / divs[i], m) == 1) {
                ok = false;
                break;
            }
        }
        if (ok) return g;
    }
}

} // namespace math

namespace convolution {

namespace type_traits {

template<typename T>
struct is_complex : std::false_type {
    using type = T;
};

template<typename T>
struct is_complex<std::complex<T>> : std::true_type {
    using type = T;
};

template<typename T>
constexpr bool is_modint() {
    return !is_complex<T>::value && !std::is_arithmetic<T>::value;
}

} // namespace type_traits

template<typename T>
std::vector<T> convolution_naive(const std::vector<T>& a, const std::vector<T>& b) {
    std::vector<T> c(a.size() + b.size() - 1);
    if (a.size() > b.size()) {
        for (size_t i = 0; i < a.size(); ++i) {
            for (size_t j = 0; j < b.size(); ++j) {
                c[i + j] += a[i] * b[j];
            }
        }
    } else {
        for (size_t j = 0; j < b.size(); ++j) {
            for (size_t i = 0; i < a.size(); ++i) {
                c[i + j] += a[i] * b[j];
            }
        }
    }
    return c;
}

template<typename T>
class FFTBase {
protected:
    std::vector<T> roots;

public:
    FFTBase() = default;
    virtual ~FFTBase() = default;

    void fft(std::vector<T>& a, int type) {
        reinit(a.size());
        butterfly(a);
        size_t n = a.size();
        for (size_t k = 1; k < n; k *= 2) {
            for (size_t i = 0; i < n; i += 2 * k) {
                for (size_t j = 0; j < k; j++) {
                    T u = a[i + j];
                    T v = a[i + j + k] * roots[j + k];
                    a[i + j] = u + v;
                    a[i + j + k] = u - v;
                }
            }
        }
        if (type == -1) {
            std::reverse(a.begin() + 1, a.end());
            const T inv_n = T(1) / T(n);
            for (size_t i = 0; i < n; ++i) {
                a[i] *= inv_n;
            }
        }
    }

private:
    virtual void reinit(size_t n) = 0;

    void butterfly(std::vector<T>& a) {
        size_t n = a.size();
        for (size_t i = 1, j = n / 2; i + 1 < n; ++i) {
            if (i < j) {
                std::swap(a[i], a[j]);
            }
            size_t k = n / 2;
            while (j >= k) {
                j -= k;
                k /= 2;
            }
            if (j < k) {
                j += k;
            }
        }
    }
};

template<typename T, typename MT = std::decay_t<decltype(T::mod())>>
class FFTModInt : public FFTBase<T> {
private:
    void reinit(size_t n) override {
        static MT mod;
        if (mod != T::mod()) {
            mod = T::mod();
            this->roots.clear();
        }
        if (this->roots.size() >= n) {
            return;
        }
        static std::unordered_map<MT, MT> primitive_root;
        auto itr = primitive_root.find(mod);
        if (itr == primitive_root.end()) {
            itr = primitive_root.emplace(mod, math::primitive_root_constexpr(mod)).first;
        }
        const T w = math::power(T(itr->second), (mod - 1) / n);
        this->roots.resize(n);
        this->roots[n / 2] = T(1);
        for (size_t i = 1; i < n / 2; ++i) {
            this->roots[i + n / 2] = this->roots[(i - 1) + n / 2] * w;
        }
        for (size_t i = n / 2 - 1; i > 0; --i) {
            this->roots[i] = this->roots[i * 2];
        }
    }
};

template<typename T>
class FFTComplex : public FFTBase<std::complex<T>> {
protected:
    void reinit(size_t n) override {
        if (this->roots.size() >= n) {
            return;
        }
        static const T PI = std::acos(T(-1));
        this->roots.resize(n);
        for (size_t i = 0; i <= n / 8; ++i) {
            this->roots[i + n / 2] = std::complex<T>(std::cos(2 * PI / n * i), std::sin(2 * PI / n * i));
        }
        for (size_t i = n / 8 + 1; i <= n / 4; ++i) {
            this->roots[i + n / 2] = std::complex<T>(this->roots[(n / 4 - i) + n / 2].imag(), this->roots[(n / 4 - i) + n / 2].real());
        }
        for (size_t i = n / 4 + 1; i < n / 2; ++i) {
            this->roots[i + n / 2] = std::complex<T>(-this->roots[(n / 2 - i) + n / 2].real(), this->roots[(n / 2 - i) + n / 2].imag());
        }
        for (size_t i = n / 2 - 1; i > 0; --i) {
            this->roots[i] = this->roots[i * 2];
        }
    }
};

template<typename T, typename VT, typename FT>
std::vector<VT> convolution_impl(const std::vector<T>& a, const std::vector<T>& b) {
    size_t len = a.size() + b.size() - 1;
    size_t n = 1;
    while (n < len) {
        n *= 2;
    }
    static FT fft;
    std::vector<VT> ta(n), tb(n);
    for (size_t i = 0; i < a.size(); ++i) {
        ta[i] = a[i];
    }
    fft.fft(ta, 1);
    if (&a == &b) {
        for (size_t i = 0; i < n; ++i) {
            tb[i] = ta[i];
        }
    } else {
        for (size_t i = 0; i < b.size(); ++i) {
            tb[i] = b[i];
        }
        fft.fft(tb, 1);
    }
    for (size_t i = 0; i < n; ++i) {
        ta[i] *= tb[i];
    }
    fft.fft(ta, -1);
    ta.resize(len);
    return ta;
}

template<typename T>
class FFTConjOpt : public FFTComplex<T> {
public:
    void dft(std::vector<std::complex<T>>& a) {
        this->reinit(a.size());
        size_t n = a.size() / 2;
        for (size_t i = 0; i < n; ++i) {
            a[i] = std::complex<T>(a[i * 2].real(), a[i * 2 + 1].real());
        }
        a.resize(n);
        this->fft(a, 1);
        a.resize(n * 2);
        for (size_t i = 0; i <= n / 2; ++i) {
            size_t j = (n - i) & (n - 1);
            std::complex<T> u = (a[i] + std::conj(a[j])) / std::complex<T>(2, 0);
            std::complex<T> v = (a[i] - std::conj(a[j])) * this->roots[i + n] / std::complex<T>(0, 2);
            a[i] = u + v;
            a[i + n] = u - v;
            if (j != i) {
                a[j] = std::conj(a[i + n]);
                a[j + n] = std::conj(a[i]);
            }
        }
    }

    void idft(std::vector<std::complex<T>>& a) {
        this->reinit(a.size());
        size_t n = a.size() / 2;
        for (size_t i = 0; i < n; ++i) {
            a[i] = (a[i] + a[i + n]) / std::complex<T>(2, 0) - (a[i] - a[i + n]) * std::conj(this->roots[i + n]) / std::complex<T>(0, 2);
        }
        a.resize(n);
        this->fft(a, -1);
        a.resize(n * 2);
        for (ssize_t i = n - 1; i >= 0; --i) {
            a[i * 2 + 1] = a[i].imag();
            a[i * 2] = a[i].real();
        }
    }
};

template<typename T, typename CT = double, typename VT = long long>
std::vector<T> convolution_mod_impl(const std::vector<T>& a, const std::vector<T>& b) {
    size_t len = a.size() + b.size() - 1;
    size_t n = 1;
    while (n < len) {
        n *= 2;
    }
    VT m = std::sqrt(T::mod());
    while (m * m < T::mod()) {
        ++m;
    }
    auto split = [&] (VT c) {
        if (2 * c >= T::mod()) {
            c -= T::mod();
        }
        VT x = ((c % m) + m) % m;
        if (2 * x >= m) {
            x -= m;
        }
        return std::complex<CT>(x, (c - x) / m);
    };
    static FFTConjOpt<CT> fft;
    std::vector<std::complex<CT>> ta(n), tb(n);
    for (size_t i = 0; i < a.size(); ++i) {
        ta[i] = split(a[i].val());
    }
    fft.fft(ta, 1);
    if (&a == &b) {
        for (size_t i = 0; i < n; ++i) {
            tb[i] = ta[i];
        }
    } else {
        for (size_t i = 0; i < b.size(); ++i) {
            tb[i] = split(b[i].val());
        }
        fft.fft(tb, 1);
    }
    for (size_t i = 0; i <= n / 2; ++i) {
        size_t j = (n - i) & (n - 1);
        std::complex<CT> pa[2] = {(ta[i] + std::conj(ta[j])) / std::complex<CT>(2, 0),
                                  (ta[i] - std::conj(ta[j])) / std::complex<CT>(0, 2)};
        std::complex<CT> pb[2] = {(tb[i] + std::conj(tb[j])) / std::complex<CT>(2, 0),
                                  (tb[i] - std::conj(tb[j])) / std::complex<CT>(0, 2)};
        std::complex<CT> u = pa[0] * pb[0];
        std::complex<CT> v = pa[1] * pb[1] * std::complex<CT>(0, 1);
        ta[i] = u + v;
        tb[i] = pa[0] * pb[1] + pa[1] * pb[0];
        if (j != i) {
            ta[j] = std::conj(u - v);
            tb[j] = std::conj(tb[i]);
        }
    }
    fft.fft(ta, -1);
    fft.idft(tb);
    std::vector<T> t(len);
    for (size_t i = 0; i < len; ++i) {
        T tt[3] = {VT(std::llround(ta[i].real())), VT(std::llround(tb[i].real())), VT(std::llround(ta[i].imag()))};
        t[i] = tt[0] + tt[1] * m + tt[2] * m * m;
    }
    return t;
}

template<typename T, std::enable_if_t<type_traits::is_modint<T>()>* = nullptr,
         typename MT = std::decay_t<decltype(T::mod())>>
std::vector<T> convolution(const std::vector<T>& a, const std::vector<T>& b) {
    size_t len = a.size() + b.size() - 1;
    size_t n = 1;
    while (n < len) {
        n *= 2;
    }
    static MT mod;
    static bool prime;
    if (mod != T::mod()) {
        mod = T::mod();
        prime = math::is_prime_constexpr(mod);
    }
    if (prime && (mod - 1) % n == 0) {
        return convolution_impl<T, T, FFTModInt<T>>(a, b);
    } else {
        return convolution_mod_impl<T>(a, b);
    }
}

template<typename T, std::enable_if_t<!type_traits::is_modint<T>()>* = nullptr,
         typename CT = std::conditional_t<type_traits::is_complex<T>::value, typename type_traits::is_complex<T>::type, double>>
std::vector<T> convolution(const std::vector<T>& a, const std::vector<T>& b) {
    std::vector<std::complex<CT>> ta = convolution_impl<T, std::complex<CT>, FFTComplex<CT>>(a, b);
    size_t len = a.size() + b.size() - 1;
    std::vector<T> t(len);
    if constexpr (type_traits::is_complex<T>::value) {
        for (size_t i = 0; i < len; ++i) {
            t[i] = ta[i];
        }
    } else if constexpr (std::is_floating_point<T>::value) {
        for (size_t i = 0; i < len; ++i) {
            t[i] = ta[i].real();
        }
    } else {
        for (size_t i = 0; i < len; ++i) {
            t[i] = std::llround(ta[i].real());
        }
    }
    return t;
}

} // namespace convolution

namespace polynomial {

template<typename T>
class Poly : public std::vector<T> {
public:
    Poly() : std::vector<T>() {}
    explicit Poly(size_t count) : std::vector<T>(count) {}
    Poly(size_t count, const T& value) : std::vector<T>(count, value) {}

    Poly(const std::vector<T>& other) : std::vector<T>(other) {}
    Poly(std::vector<T>&& other) : std::vector<T>(std::move(other)) {}
    Poly(const std::initializer_list<T>& init) : std::vector<T>(init) {}

    template<class InputIterator>
    Poly(InputIterator first, InputIterator last) : std::vector<T>(first, last) {}

public:
    Poly& resize(size_t k) {
        this->std::vector<T>::resize(k);
        return *this;
    }
    Poly& rev(bool strip = true) {
        std::reverse(this->begin(), this->end());
        return (strip ? this->strip() : *this);
    }
    Poly& shift(int k, bool strip = true) {
        if (k >= 0) {
            this->insert(this->begin(), k, T(0));
        } else {
            this->erase(this->begin(), this->begin() + std::min(this->size(), static_cast<size_t>(-k)));
        }
        return (strip ? this->strip() : *this);
    }
    Poly& strip() {
        while (!this->empty() && this->back() == T(0)) {
            this->pop_back();
        }
        return *this;
    }
    Poly& trunc(size_t k, bool strip = true) {
        this->resize(std::min(this->size(), k));
        return (strip ? this->strip() : *this);
    }

    friend Poly presize(const Poly& a, size_t k) {
        Poly b(a);
        b.resize(k);
        return b;
    }
    friend Poly prev(const Poly& a, bool strip = true) {
        Poly b(a);
        b.rev(strip);
        return b;
    }
    friend Poly pshift(const Poly& a, int k, bool strip = true) {
        Poly b(a);
        b.shift(k, strip);
        return b;
    }
    friend Poly pstrip(const Poly& a) {
        Poly b(a);
        b.strip();
        return b;
    }
    friend Poly ptrunc(const Poly& a, size_t k, bool strip = true) {
        Poly b = Poly(a.begin(), a.begin() + std::min(a.size(), k));
        if (strip) {
            b.strip();
        }
        return b;
    }

public:
    T operator () (const T& x) const {
        T y(0);
        for (ssize_t i = this->size() - 1; i >= 0; --i) {
            y = y * x + (*this)[i];
        }
        return y;
    }
    Poly& operator += (const Poly& b) {
        this->resize(std::max(this->size(), b.size()));
        for (size_t i = 0; i < b.size(); ++i) {
            (*this)[i] += b[i];
        }
        return this->strip();
    }
    Poly& operator -= (const Poly& b) {
        this->resize(std::max(this->size(), b.size()));
        for (size_t i = 0; i < b.size(); ++i) {
            (*this)[i] -= b[i];
        }
        return this->strip();
    }
    Poly& operator *= (const Poly& b) {
        return *this = *this * b;
    }
    Poly& operator /= (const Poly& b) {
        if (this->size() < b.size()) {
            return *this = Poly();
        }
        size_t len = this->size() - b.size() + 1;
        return (this->rev().trunc(len) *= prev(b).inv(len)).resize(len).rev();
    }
    Poly& operator %= (const Poly& b) {
        return *this -= *this / b * b;
    }

    Poly operator + (const Poly& b) const {
        Poly a(*this);
        a += b;
        return a;
    }
    Poly operator - (const Poly& b) const {
        Poly a(*this);
        a -= b;
        return a;
    }
    Poly operator * (const Poly& b) const {
        if (this->size() == 0 || b.size() == 0) {
            return Poly();
        }
        Poly x;
        if (std::min(this->size(), b.size()) <= 50u) {
            x = Poly(convolution::convolution_naive<T>(*this, b));
        } else {
            x = Poly(convolution::convolution<T>(*this, b));
        }
        x.strip();
        return x;
    }
    Poly operator / (const Poly& b) const {
        Poly a(*this);
        a /= b;
        return a;
    }
    Poly operator % (const Poly& b) const {
        Poly a(*this);
        a %= b;
        return a;
    }

public:
    Poly inv(size_t m) const {
        Poly x{T(1) / (*this)[0]};
        size_t k = 1;
        while (k < m) {
            k *= 2;
            x = x * Poly{2} - (x * x * ptrunc(*this, k)).trunc(k);
        }
        x.trunc(m);
        return x;
    }
    Poly deriv() const {
        if (this->empty()) {
            return Poly();
        }
        Poly x(this->size() - 1);
        for (size_t i = 0; i + 1 < this->size(); ++i) {
            x[i] = (*this)[i + 1] * T(i + 1);
        }
        x.strip();
        return x;
    }
    Poly integr() const {
        static std::vector<T> inv(1);
        while (inv.size() <= this->size()) {
            inv.resize(inv.size() * 2);
            for (size_t i = inv.size() / 2; i < inv.size(); ++i) {
                inv[i] = T(1) / T(i);
            }
        }
        Poly x(this->size() + 1);
        for (size_t i = 0; i < this->size(); ++i) {
            x[i + 1] = (*this)[i] * inv[i + 1];
        }
        x.strip();
        return x;
    }
    Poly log(size_t m) const {
        if (m == 0) {
            return Poly();
        }
        return (this->deriv().trunc(m) * this->inv(m)).trunc(m - 1).integr();
    }
    Poly exp(size_t m) const {
        Poly x{1};
        size_t k = 1;
        while (k < m) {
            k *= 2;
            (x *= Poly{1} - x.log(k) + ptrunc(*this, k)).trunc(k);
        }
        x.trunc(m);
        return x;
    }
    Poly pow(long long k, size_t m) const {
        if (k < 0) {
            return this->inv(m).pow(-k, m);
        }
        if (k == 0) {
            return Poly{1};
        }
        size_t i = 0;
        while (i < this->size() && (*this)[i] == T(0)) {
            i++;
        }
        if (i == this->size() || i >= (m + k - 1) / k) {
            return Poly();
        }
        T v = (*this)[i];
        return ((pshift(*this, -i) * Poly{T(1) / v}).log(m - i * k) * Poly{k}).exp(m - i * k).shift(i * k) * Poly{math::power(v, k)};
    }
    Poly sqrt(size_t m) const {
        Poly x{1};
        const Poly inv_2{T(1) / T(2)};
        size_t k = 1;
        while (k < m) {
            k *= 2;
            x = (x + (ptrunc(*this, k) * x.inv(k)).trunc(k)) * inv_2;
        }
        x.trunc(m);
        return x;
    }
    Poly mulT(Poly b) const {
        if (b.size() == 0) {
            return Poly();
        }
        int n = b.size();
        std::reverse(b.begin(), b.end());
        return ((*this) * b).shift(-(n - 1));
    }
    std::vector<T> eval(std::vector<T> x) const {
        if (this->size() == 0) {
            return std::vector<T>(x.size(), 0);
        }
        const int n = std::max(x.size(), this->size());
        std::vector<Poly> q(4 * n);
        std::vector<T> ans(x.size());
        x.resize(n);
        std::function<void(int, int, int)> build = [&](int p, int l, int r) {
            if (r - l == 1) {
                q[p] = Poly{1, -x[l]};
            } else {
                int m = (l + r) / 2;
                build(2 * p, l, m);
                build(2 * p + 1, m, r);
                q[p] = q[2 * p] * q[2 * p + 1];
            }
        };
        build(1, 0, n);
        std::function<void(int, int, int, const Poly &)> work = [&](int p, int l, int r, const Poly &num) {
            if (r - l == 1) {
                if (l < int(ans.size())) {
                    ans[l] = num[0];
                }
            } else {
                int m = (l + r) / 2;
                work(2 * p, l, m, num.mulT(q[2 * p + 1]).resize(m - l));
                work(2 * p + 1, m, r, num.mulT(q[2 * p]).resize(r - m));
            }
        };
        work(1, 0, n, mulT(q[1].inv(n)));
        return ans;
    }
};

} // nameapace polynomial

#endif // CPLIBRARY_POLYNOMIAL_HPP
