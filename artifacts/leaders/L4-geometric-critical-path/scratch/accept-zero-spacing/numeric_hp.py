#!/usr/bin/env python3
"""mpmath high-precision cross-check of the smallest numeric gaps found with
scipy DOP853, plus exact analytic values for the constant profiles."""
import math
import mpmath as mp

mp.mp.dps = 60
PI = mp.pi


def solve(k):
    def f(t, y):
        return [y[1], -k(t) * y[0]]
    return mp.odefun(f, mp.mpf(0), [mp.mpf(0), mp.mpf(1)], tol=mp.mpf('1e-55'))


def first_zero(k, tmax):
    sol = solve(k)
    # u > 0 right after 0; scan for the first sign change
    t = mp.mpf('0.05')
    prev = sol(t)[0]
    while t < tmax:
        t2 = t + mp.mpf('0.05')
        cur = sol(t2)[0]
        if cur < 0:
            lo, hi = t, t2
            for _ in range(200):
                mid = (lo + hi) / 2
                if sol(mid)[0] > 0:
                    lo = mid
                else:
                    hi = mid
            return (lo + hi) / 2, sol
        prev, t = cur, t2
    return None, sol


def report(name, k, expected_bound, tmax=8):
    z, sol = first_zero(k, mp.mpf(tmax))
    d = z - expected_bound
    print(f"{name:28s} c2 = {mp.nstr(z, 30):>32s}")
    print(f"{'':28s} c2 - pi/sqrtK = {mp.nstr(d, 12)}")
    return d


def main():
    K = mp.mpf(1)
    bound = PI / mp.sqrt(K)
    print("== constant profiles (exact: c2 = pi/sqrt(k)) ==")
    for kk in ['1.001', '1.0', '0.999', '0.5']:
        kk = mp.mpf(kk)
        z, _ = first_zero(lambda t, kk=kk: kk, mp.mpf(8))
        exact = PI / mp.sqrt(kk)
        print(f"k={mp.nstr(kk,5):>6s}  c2={mp.nstr(z,25)}  exact={mp.nstr(exact,25)}  "
              f"diff={mp.nstr(z-exact,5)}")

    print("== tiny smooth excess k = 1 + eps*(t/pi)^20 ==")
    for eps in ['1e-3', '1e-6', '1e-9']:
        e = mp.mpf(eps)
        k = lambda t, e=e: 1 + e * (t / PI) ** 20
        report(f"power20_eps={eps}", k, bound)

    print("== late Gaussian excess k = 1 + 0.5 exp(-((t-(pi-0.05))/0.02)^2) ==")
    c = PI - mp.mpf('0.05')
    k = lambda t: 1 + mp.mpf('0.5') * mp.e ** (-((t - c) / mp.mpf('0.02')) ** 2)
    report("late_gauss_0.05", k, bound)

    print("== k <= 1 nonconstant: k = 1 - 0.15(1+cos 2t) ==")
    k = lambda t: 1 - mp.mpf('0.15') * (1 + mp.cos(2 * t))
    z, _ = first_zero(k, mp.mpf(8))
    print(f"{'below_sin2':28s} c2 - pi = {mp.nstr(z - bound, 12)}")

    print("== exact values ==")
    print("pi/sqrt(1.001) - pi =", mp.nstr(PI / mp.sqrt(mp.mpf('1.001')) - PI, 15))
    print("pi/sqrt(0.999) - pi =", mp.nstr(PI / mp.sqrt(mp.mpf('0.999')) - PI, 15))
    print("pi/sqrt(0.5)   - pi =", mp.nstr(PI / mp.sqrt(mp.mpf('0.5')) - PI, 15))


if __name__ == "__main__":
    main()
