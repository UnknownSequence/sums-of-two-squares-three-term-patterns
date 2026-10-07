"""
Numerical tools for the harmonics phi_{l1,l2}(a_u, nu) and P_nu^{(l1,l2)} of
Grimmelt--Merikoski, "Weighted averages of SL_2(R) automorphic kernel, part I"
(arXiv:2505.00489), Sections 2.1, 2.4, 2.7 and 4.  All conventions follow that paper:

  n[x] = [[1,x],[0,1]],  a[y] = diag(sqrt y, 1/sqrt y),  k[t] = [[cos t, sin t],[-sin t, cos t]],
  g = n[x] a[y] k[theta]  (Iwasawa),   g = k[phi] a[e^{-rho}] k[vartheta]  (Cartan),
  cosh(rho) = 2u+1,  a_u = a[e^{-rho}],
  phi_l(g,nu) = y^{1/2+nu} e^{i l theta}                         (2.19)
  phi_{l1,l2}(g,nu) = (1/2pi) int_0^{2pi} phi_{l2}(k[phi] g, nu) e^{-i l1 phi} dphi   (2.20)

Only numpy/scipy are used.
"""
import numpy as np
from scipy.special import loggamma, hyp2f1, gammaln

TWO_PI = 2.0 * np.pi


def iwasawa(a, b, c, d):
    """Iwasawa coordinates (x, y, theta) of g=[[a,b],[c,d]] in the conventions of (2.1)-(2.2)."""
    den = c * c + d * d
    y = 1.0 / den
    x = (a * c + b * d) / den
    theta = np.arctan2(-c, d)          # cos(theta)=d*sqrt(y), sin(theta)=-c*sqrt(y)
    return x, y, theta


def kmat(t):
    return np.array([[np.cos(t), np.sin(t)], [-np.sin(t), np.cos(t)]])


def a_u_entries(u):
    rho = np.arccosh(2 * u + 1)
    return np.exp(-rho / 2), np.exp(rho / 2)   # a_u = diag(e^{-rho/2}, e^{rho/2})


def phi_direct(u, nu, l1, l2, N=1 << 16):
    """phi_{l1,l2}(a_u,nu) straight from the definition (2.20), trapezoid rule in phi."""
    p = np.arange(N) * TWO_PI / N
    e1, e2 = a_u_entries(u)
    # k[p] a_u = [[cos p e1, sin p e2], [-sin p e1, cos p e2]]
    a = np.cos(p) * e1
    b = np.sin(p) * e2
    c = -np.sin(p) * e1
    d = np.cos(p) * e2
    x, y, th = iwasawa(a, b, c, d)
    vals = y ** (0.5 + nu) * np.exp(1j * l2 * th) * np.exp(-1j * l1 * p)
    return vals.mean()


def phi_lemma41(u, nu, l1, l2, N=None):
    """Second formula of Lemma 4.1 (trapezoid rule)."""
    if N is None:
        N = int(max(1 << 14, 64 * (u + 1)))
    rho = np.arccosh(2 * u + 1)
    C, S = np.cosh(rho / 2), np.sinh(rho / 2)
    p = np.arange(N) * TWO_PI / N
    z = C + S * np.exp(1j * p)
    zb = C + S * np.exp(-1j * p)
    vals = z ** (-0.5 - nu - l2 / 2) * zb ** (-0.5 - nu + l2 / 2) * np.exp(1j * (l2 - l1) * p / 2)
    return vals.mean()


def phi_lemma41_first(u, nu, l1, l2, N=None):
    """First formula of Lemma 4.1."""
    if N is None:
        N = int(max(1 << 14, 64 * (u + 1)))
    p = np.arange(N) * TWO_PI / N
    r = np.sqrt(1 + 1 / u)
    base = (2 * u + 1 + 2 * np.sqrt(u * (u + 1)) * np.cos(p)) ** (-0.5 - nu)
    ratio = ((r + np.exp(-1j * p)) / (r + np.exp(1j * p))) ** (l2 / 2)
    vals = base * ratio * np.exp(1j * (l2 - l1) * p / 2)
    return vals.mean()


def phi_all_l1(u, nu, l2, N):
    """All Fourier modes at once: returns dict m -> phi_{l1,l2}(a_u,nu) with l1 = l2 - 2m...
    We return an array c[m] for m in fftfreq order where l1 = l2 + 2m."""
    rho = np.arccosh(2 * u + 1)
    C, S = np.cosh(rho / 2), np.sinh(rho / 2)
    p = np.arange(N) * TWO_PI / N
    z = C + S * np.exp(1j * p)
    zb = C + S * np.exp(-1j * p)
    f = z ** (-0.5 - nu - l2 / 2) * zb ** (-0.5 - nu + l2 / 2)
    # phi_{l1,l2} = mean( f * e^{i (l2-l1) p / 2} ) = mean(f e^{-i m p}) with m=(l1-l2)/2
    c = np.fft.fft(f) / N
    m = np.fft.fftfreq(N, d=1.0 / N).astype(int)
    l1 = l2 + 2 * m
    return l1, c


def hyp2f1_series(a, b, c, z, tol=1e-17, maxit=100000):
    """Gauss series, for complex parameters and |z| < 1 (used only for z <= 0.9)."""
    s, t, n = 1.0 + 0j, 1.0 + 0j, 0
    while n < maxit:
        t *= (a + n) * (b + n) / ((c + n) * (n + 1)) * z
        s += t
        n += 1
        if abs(t) < tol * abs(s) and n > 5:
            break
    return s


def phi_ll_large_u(u, nu, l, terms=60):
    """phi_{l,l}(a_u,nu) for large u via the connection formula z -> 1-z (real 0<nu<1/2, l even or odd).
    phi = (u+1)^{-1/2-nu} [ A * F(a,b;a+b;w) + w^{-2nu} B * F(1-a,1-b;1-2nu;w) ],  w = 1/(u+1),
    a = 1/2+nu+l/2, b = 1/2+nu-l/2, A = Gamma(-2nu)/(Gamma(1-a)Gamma(1-b)), B = Gamma(2nu)/(Gamma(a)Gamma(b))."""
    from scipy.special import gamma, rgamma
    a, b = 0.5 + nu + l / 2, 0.5 + nu - l / 2
    w = 1.0 / (u + 1)
    A = gamma(-2 * nu) * rgamma(1 - a) * rgamma(1 - b)
    B = gamma(2 * nu) * rgamma(a) * rgamma(b)
    F1 = hyp2f1_series(a, b, a + b, w)          # c-a-b = 0 here is fine for the series in w (|w| small)
    F2 = hyp2f1_series(1 - a, 1 - b, 1 - 2 * nu, w)
    return ((u + 1) ** (-0.5 - nu) * (A * F1 + w ** (-2 * nu) * B * F2)).real


def lemma43_main(u, nu, l):
    """Main term of Lemma 4.3 as computed here: (Gamma(2nu)cos(pi nu)/pi)(-1)^{l/2} G(1/2+|l|/2-nu)/G(1/2+|l|/2+nu) u^{-1/2+nu} (l even)."""
    from scipy.special import gamma
    n = abs(l) // 2
    return (gamma(2 * nu) * np.cos(np.pi * nu) / np.pi * (-1) ** n
            * np.exp(gammaln(0.5 + n - nu) - gammaln(0.5 + n + nu)) * u ** (-0.5 + nu))


def phi_ll_hyp(u, nu, l):
    """phi_{l,l}(a_u,nu) = (u+1)^{-1/2-nu} 2F1(1/2+nu+l/2, 1/2+nu-l/2; 1; u/(u+1)).
    scipy's hyp2f1 for real nu; Gauss series (z<=0.9) or Lemma 4.1 quadrature otherwise."""
    z = u / (u + 1)
    if np.isrealobj(nu) or (isinstance(nu, complex) and nu.imag == 0):
        nur = float(np.real(nu))
        return (u + 1) ** (-0.5 - nur) * hyp2f1(0.5 + nur + l / 2, 0.5 + nur - l / 2, 1.0, z)
    if z <= 0.9:
        return (u + 1) ** (-0.5 - nu) * hyp2f1_series(0.5 + nu + l / 2, 0.5 + nu - l / 2, 1.0, z)
    return phi_lemma41(u, nu, l, l)


# ---------- unitary normalisation (2.27), (2.28), (2.30) ----------

def logG(nu, l, kappa=0, k=None):
    """log G(nu,l) of (2.27) for l>=0, l = kappa mod 2 (principal/complementary) or discrete series weight k."""
    if k is None:
        return (-(l - kappa) / 2) * np.log(2) + 0.5 * (
            loggamma(nu + (1 + kappa) / 2) + loggamma(-nu + (1 + kappa) / 2)
            - loggamma(nu + (1 + l) / 2) - loggamma(-nu + (1 + l) / 2))
    else:
        return (-(l - k) / 2) * np.log(2) + 0.5 * (gammaln(k) - gammaln((l + k) / 2) - gammaln((l - k) / 2 + 1))


def logGphi(nu, l, kappa=0):
    """log G_phi(nu,l) of (2.28)."""
    return (-(l - kappa) / 2) * np.log(2) + loggamma((1 + kappa) / 2 + nu) - loggamma((1 + l) / 2 + nu)


def norm_factor(nu, l1, l2, kappa=0, k=None):
    """G_phi(nu,|l1|) G(nu,|l2|) / (G_phi(nu,|l2|) G(nu,|l1|))  -- the factor in (2.30)."""
    a1, a2 = abs(l1), abs(l2)
    return np.exp(logGphi(nu, a1, kappa) + logG(nu, a2, kappa, k) - logGphi(nu, a2, kappa) - logG(nu, a1, kappa, k))


def casimir_residual(pfun, u, nu, l1, l2, h=None):
    """Residual of Omega P = (1/4 - nu^2) P for P = e^{i l1 phi} p(u) e^{i l2 vartheta}, using (2.12)."""
    if h is None:
        h = 1e-3 * max(u, 1e-2)
    us = u + h * np.arange(-3, 4)
    pv = np.array([pfun(x) for x in us])
    # 7-point central differences
    d1 = (-pv[0] + 9 * pv[1] - 45 * pv[2] + 45 * pv[4] - 9 * pv[5] + pv[6]) / (60 * h)
    d2 = (2 * pv[0] - 27 * pv[1] + 270 * pv[2] - 490 * pv[3] + 270 * pv[4] - 27 * pv[5] + 2 * pv[6]) / (180 * h * h)
    p0 = pv[3]
    lhs = (-u * (u + 1) * d2 - (2 * u + 1) * d1
           + (l1 ** 2 + l2 ** 2) / (16 * u * (u + 1)) * p0
           - (2 * u + 1) * l1 * l2 / (8 * u * (u + 1)) * p0)
    return lhs, (0.25 - nu ** 2) * p0


def gbinom(a, j):
    """generalised binomial coefficient binom(a, j) for real a, integer j >= 0"""
    r = 1.0
    for i in range(j):
        r *= (a - i) / (i + 1)
    return r


def phi_discrete(u, kw, l1, l2):
    """Stable evaluation of phi_{l1,l2}(a_u,(kw-1)/2) for l2 >= kw, l2 = kw mod 2 (finite sum):
    phi = (u+1)^{-kw/2} sum_{k=0}^{b} binom(a,k+m) binom(b,k) (u/(u+1))^{k+m/2},
    a = -(kw+l2)/2, b = (l2-kw)/2, m = (l1-l2)/2."""
    a = -(kw + l2) / 2
    b = (l2 - kw) // 2
    m = (l1 - l2) // 2
    t = u / (u + 1)
    s = 0.0
    for k in range(0, b + 1):
        if k + m < 0:
            continue
        s += gbinom(a, k + m) * gbinom(b, k) * t ** (k + m / 2)
    return (u + 1) ** (-kw / 2) * s
