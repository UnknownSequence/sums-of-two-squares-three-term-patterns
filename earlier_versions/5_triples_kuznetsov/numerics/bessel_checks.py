"""
Numerical checks of the K-Bessel representations used in Section 6 of the paper (Lemmas 6.1 and 6.2).

For real t (= kappa below) we evaluate K_{it}(y) accurately through the convergent residue series

    K_{it}(y) = Re[ Gamma(it) (y/2)^{-it} sum_{k>=0} (-1)^k (y/2)^{2k} / (k! prod_{m=1}^k (it - m)) ],

which is the full Mellin--Barnes residue expansion. Every term carries the factor Gamma(it), so there is no
cancellation, and the relative accuracy is close to machine precision even when K_{it}(y) ~ e^{-pi|t|/2} is tiny.
The k = 0 term is the pair of residues of Lemma 6.2; the terms k >= 1 give the remainder exactly.
We cross-check the series against a contour-shifted quadrature (1/2) int_R exp(-y cosh(v+i b) + i t (v+i b)) dv.

 (1) the representation K_nu(y) = (1/2) int_0^infty exp(-(y/2)(v+1/v)) v^{nu-1} dv of Lemma 6.1, for nu = it
     (t real) and nu = theta real, against the series / scipy's kv;
 (2) Lemma 6.2: residues + the integral on Re w = -3/2 (trapezoid rule), against the series;
 (3) the remainder in Lemma 6.2 is NOT pointwise O(y^{3/2}|t|^{-5/2}e^{-pi|t|/2}) (for small y it is of order
     y^2|t|^{-3/2}e^{-pi|t|/2}); the paper only uses its average against a smooth weight in s, which decays in |t|.
     We print both the pointwise maximum over s in [1/2,1] and the smooth average, using the exact remainder.
Run: python3 bessel_checks.py
"""
import warnings
import numpy as np
from scipy.integrate import quad, IntegrationWarning
warnings.filterwarnings("ignore", category=IntegrationWarning)
from scipy.special import kv, loggamma

def series_terms_sum(t, y, start):
    """sum_{k>=start} (-1)^k (y/2)^{2k} / (k! prod_{m=1}^k (it - m)), vectorised in y"""
    y = np.asarray(y, dtype=float)
    term = np.ones_like(y, dtype=complex)
    total = np.zeros_like(y, dtype=complex)
    if start == 0:
        total += term
    for k in range(1, 400):
        term = term * (-(y / 2) ** 2) / (k * (1j * t - k))
        if k >= start:
            total += term
        if np.all(np.abs(term) < 1e-20 * np.maximum(np.abs(total), 1e-300)):
            break
    return total

def K_series(t, y):
    """K_{it}(y) for real t != 0"""
    y = np.asarray(y, dtype=float)
    pref = np.exp(loggamma(1j * t)) * np.exp(-1j * t * np.log(y / 2))
    return (pref * series_terms_sum(t, y, 0)).real

def remainder_exact(t, y):
    """K_{it}(y) minus the two residues (1/2)Gamma(+-it)(y/2)^{-+it}"""
    y = np.asarray(y, dtype=float)
    pref = np.exp(loggamma(1j * t)) * np.exp(-1j * t * np.log(y / 2))
    return (pref * series_terms_sum(t, y, 1)).real

def residues(t, y):
    return (np.exp(loggamma(1j * t)) * np.exp(-1j * t * np.log(y / 2))).real

def K_shift(t, y, b=1.45):
    """(1/2) int_R exp(-y cosh(v + i b) + i t (v + i b)) dv, |b| < pi/2 (contour shift of the cosh integral)"""
    f = lambda v: 0.5 * np.exp(-y * np.cosh(v + 1j * b) + 1j * t * (v + 1j * b))
    vmax = np.arccosh(1 + 80.0 / (y * np.cos(b)))
    re = quad(lambda v: f(v).real, -vmax, vmax, limit=4000, epsabs=0, epsrel=1e-13)[0]
    return re

def K_v_integral(nu, y):
    """(1/2) int_0^infty exp(-(y/2)(v+1/v)) v^{nu-1} dv, with v = e^s"""
    s0 = np.arccosh(1 + 60.0 / y)
    if np.isreal(nu):
        f = lambda s: 0.5 * np.exp(-y * np.cosh(s)) * np.exp(np.real(nu) * s)
        return quad(f, -s0, s0, limit=2000, epsabs=0, epsrel=1e-13)[0]
    t = np.imag(nu)
    f = lambda s: 0.5 * np.exp(-y * np.cosh(s)) * np.cos(t * s)
    return quad(f, -s0, s0, limit=4000, epsabs=0, epsrel=1e-13)[0]

def G(w, t):
    return np.exp((w - 2) * np.log(2) + loggamma((w + 1j * t) / 2) + loggamma((w - 1j * t) / 2))

def mb_integral(t, y, sigma=-1.5):
    T = abs(t) + 60
    tau = np.linspace(-T, T, 400001)
    w = sigma + 1j * tau
    vals = G(w, t) * np.exp(-w * np.log(y))
    return (np.trapezoid(vals, tau) / (2 * np.pi)).real

out = []
def say(s):
    print(s); out.append(s)

say("(0) residue series versus contour-shifted quadrature (t real):")
worst = 0
for t in [0.3, 1.0, 2.5, 6.0, 10.0, 15.0]:
    for y in [1e-3, 0.02, 0.4, 2.0]:
        a, b = K_series(t, y), K_shift(t, y)
        worst = max(worst, abs(a - b) / abs(a))
say(f"   max relative difference = {worst:.2e}")

say("(1) v-integral representation (Lemma 6.1):")
worst = 0
for nu in [0.0, 0.3j, 1.0j, 7.5j, 0.05, 0.109375, 0.4]:
    for y in [1e-3, 0.05, 0.7, 3.0]:
        ref = kv(np.real(nu), y) if np.isreal(nu) else K_series(np.imag(nu), y)
        worst = max(worst, abs(K_v_integral(nu, y) - ref) / abs(ref))
say(f"   max relative difference = {worst:.2e}")

say("(2) Mellin--Barnes (Lemma 6.2): K = residues + integral on Re w = -3/2 (t real, |t| >= 1):")
worst = 0
for t in [1.0, 2.5, 6.0, 15.0]:
    for y in [1e-3, 0.02, 0.4, 2.0]:
        k = K_series(t, y)
        r = residues(t, y) + mb_integral(t, y)
        scale = np.exp(-np.pi * abs(t) / 2) * abs(t) ** -0.5
        worst = max(worst, abs(k - r) / scale)
say(f"   max |K - (residues + integral)| / (|t|^(-1/2) e^(-pi|t|/2)) = {worst:.2e}  (accuracy of the trapezoid rule)")

say("(3) The pointwise remainder is NOT O(y^{3/2}|t|^{-5/2}e^{-pi|t|/2}) uniformly (for small y it is ~ y^2|t|^{-3/2}e^{-pi|t|/2});")
say("    the paper only uses its average against a smooth weight in s, which decays in |t|.  Exact remainder:")
def wbump(s):
    u = (s - 0.75) / 0.25
    return np.where(np.abs(u) < 1, np.exp(-1.0 / np.maximum(1 - u * u, 1e-300)), 0.0)
ss = np.linspace(0.5, 1.0, 2001)
wv = wbump(ss)
for y in [0.02, 0.4, 2.0]:
    say(f"   y={y}:")
    for t in [1.0, 2.5, 6.0, 10.0, 15.0, 25.0]:
        rem = remainder_exact(t, y * ss)
        avg = np.trapezoid(wv * rem, ss)
        pt = np.abs(rem).max()
        say(f"      t={t:4.1f}: avg/(y^1.5 e^-pi t/2) = {abs(avg)/(y**1.5*np.exp(-np.pi*t/2)):.2e},  "
            f"max_s|rem|/(y^1.5 t^-2.5 e^-pi t/2) = {pt/(y**1.5*t**-2.5*np.exp(-np.pi*t/2)):.2f}")
open("results_bessel.txt", "w").write("\n".join(out) + "\n")
