#!/usr/bin/env python3
"""Independent symbolic and rational checks; not a substitute for continuum proof."""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path

import sympy as s


def atan_interval(x: F, terms: int):
    total = sum(((-1) ** j * x ** (2*j+1) / (2*j+1)
                 for j in range(terms)), F(0))
    following = total + (-1) ** terms * x ** (2*terms+1)/(2*terms+1)
    return min(total, following), max(total, following)


def sqrt_interval(x: F, bits: int = 160):
    unit = 1 << bits
    k = math.isqrt((x.numerator << (2*bits)) // x.denominator)
    return F(k, unit), F(k+1, unit)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    if args.output.exists():
        raise SystemExit('refusing to overwrite evidence')
    beta = F(4608178181141995, 1125899906842624)
    mass = F(1432536998431173, 562949953421312)
    rho = 1+3*beta/32
    margin = 9-rho*mass**2
    h = F(221, 100000)
    d = 7*beta*mass/1760-F(1, 50)
    cap = F(30203, 40000)+beta*mass**2/8100
    kappa = h*d*d/(4*cap)
    # h <= 1-m sqrt(rho)/3, proved without a floating square root.
    slack_margin = 9*(1-h)**2-rho*mass**2
    assert min(beta, mass, rho, margin, h, d, cap, kappa, slack_margin) > 0
    al, au = atan_interval(F(1, 5), 80)
    bl, bu = atan_interval(F(1, 239), 24)
    pi_lo, pi_hi = 16*al-4*bu, 16*au-4*bl
    # Machin identity follows from tan(4 atan(1/5)-atan(1/239))=1
    # and that this angle lies in (0, pi/2). Alternation bounds each atan.
    assert 3 < pi_lo < pi_hi < F(22, 7)
    rl, ru = sqrt_interval(rho)
    threshold_lo, threshold_hi = 3/ru, 3/rl
    assert mass < threshold_lo
    D, K, M, Q, S, B, lam, t = s.symbols('D K M Q S B lam t', positive=True)
    P, Bcoef = D+B*S/3, 2*K+B*Q/2
    energy = P*lam**4-Bcoef*lam**2+M
    assert s.factor(energy-(M-Bcoef**2/(4*P))-P*(lam**2-Bcoef/(2*P))**2) == 0
    virial = D-K-B*Q/4+B*S/3
    square = D+(D-2*K+M)+(2*B/3)*(S-s.Rational(3,4)*Q+s.Rational(9,64)*M)-(1+3*B/32)*M
    assert s.expand(square-2*virial) == 0
    assert s.expand((t*(D-2*K+M)-B*t**2*Q/2+B*t**3*S/3)/t
                    -((D-2*K+M)-B*t*Q/2+B*t**2*S/3)) == 0
    # Independently derive kinetic Gaussian integral from derivative polynomial
    # and exact Gaussian moments, rather than evaluating c2/c4 as written.
    x, y, a, b, R = s.symbols('x y a b R', positive=True)
    real = x*x/(a**4*R**4)-1/(a*a*R*R)+y*y/(b**4*R**4)-1/(b*b*R*R)
    imag = -2*x/(a*a*R*R)
    polynomial = s.Poly(s.expand(real**2+imag**2), x, y)

    def moment(power, width):
        if power % 2:
            return 0
        return s.factorial2(power-1)*(width**2/2)**(power//2) if power else 1

    kinetic = s.simplify(sum(c*moment(i,a*R)*moment(j,b*R)
                             for (i,j),c in polynomial.terms()))
    expected = 2/(a*a*R*R)+(3/(4*a**4)+1/(2*a*a*b*b)+3/(4*b**4))/R**4
    assert s.simplify(kinetic-expected) == 0
    # Fourier radial integral, and fourth/sixth Gaussian integrals.
    r, eta = s.symbols('r eta', positive=True)
    radial = s.integrate(r/(r**4+eta), (r,0,s.oo))/(2*s.pi)
    assert s.simplify(radial-1/(8*s.sqrt(eta))) == 0
    for power in (2,4,6):
        gx=s.integrate(s.exp(-power*x*x/(2*a*a*R*R)),(x,-s.oo,s.oo))
        gy=s.integrate(s.exp(-power*y*y/(2*b*b*R*R)),(y,-s.oo,s.oo))
        actual=s.simplify(gx*gy/(s.pi*a*b*R*R)**(s.Rational(power,2)))
        want={2:1,4:1/(2*s.pi*a*b*R*R),6:1/(3*s.pi**2*a*a*b*b*R**4)}[power]
        assert s.simplify(actual-want)==0
    result = dict(status='PASS', scope='symbolic identities and exact rational inequalities; continuum proof is in D4_PHASE_VII_ANALYSIS.md',
                  beta=str(beta),mass=str(mass),rho=str(rho),margin=str(margin),
                  slack_floor=str(h),slack_squared_margin=str(slack_margin),
                  d_floor=str(d),c4_cap=str(cap),kappa_exact=str(kappa),
                  kappa_decimal_diagnostic=float(kappa),
                  threshold_interval=[str(threshold_lo),str(threshold_hi)],
                  pi_interval=[str(pi_lo),str(pi_hi)],
                  symbolic_checks=['dilation gap','improved virial square','amplitude scaling',
                                   'Gaussian kinetic from moments','Fourier integral','Gaussian M,Q,S'],
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  sympy_version=s.__version__,sampling_used_in_proof=False)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','kappa_decimal_diagnostic','symbolic_checks')}))


if __name__ == '__main__':
    main()
