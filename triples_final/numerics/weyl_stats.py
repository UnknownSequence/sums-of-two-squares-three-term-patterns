"""
Square-root cancellation in the Weyl sums for quadratic roots that appear after Poisson summation
(Section 9 of triples_final.pdf; reported in Section 14 and used in Remark 13.1):
    S_h(K) = sum_{mu = kappa d (4d), K <= mu < 2K} sum_{nu mod mu, E nu^2 + H = 0 (mu)} e(h nu / mu).
We report the number of terms n(K), the root-mean-square of |S_h|/sqrt(n(K)) over 1 <= h <= 200, and max_h |S_h|/sqrt(n).
Run: python3 weyl_stats.py
"""
import numpy as np

def roots_by_modulus(E, H, d, kappa, K):
    data = []
    for mu in range(K, 2 * K):
        if (mu - kappa * d) % (4 * d):
            continue
        nu = np.arange(mu, dtype=np.int64)
        r = np.nonzero((E * nu * nu + H) % mu == 0)[0]
        if r.size:
            data.append((mu, r))
    return data

out = []
for (E, H, d) in [(8, 1057, 89), (8, 285, 53)]:
    for kappa in (1, 3):
        for K in [20000, 100000, 300000]:
            data = roots_by_modulus(E, H, d, kappa, K)
            n = sum(r.size for _, r in data)
            hs = np.arange(1, 201)
            S = np.zeros(hs.size, dtype=complex)
            for mu, r in data:
                S += np.exp(2j * np.pi * np.outer(hs, r) / mu).sum(axis=1)
            ratio = np.abs(S) / np.sqrt(n)
            line = (f"E={E} H={H} d={d} kappa={kappa} K={K}: n={n}, rms_h |S_h|/sqrt(n) = {np.sqrt(np.mean(ratio**2)):.3f}, "
                    f"max_h |S_h|/sqrt(n) = {ratio.max():.3f}")
            print(line); out.append(line)
open("results_weyl_stats.txt", "w").write("\n".join(out) + "\n")
