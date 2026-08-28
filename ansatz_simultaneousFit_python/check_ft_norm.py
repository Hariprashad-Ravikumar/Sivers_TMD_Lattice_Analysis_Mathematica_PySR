import numpy as np
from scipy.special import gamma, kv
import math

def analytical_FT_A2BRe(x, a_re, c_re, d_re, j_re):
    abs_x = np.abs(x)
    cd_R = c_re / d_re
    term1_R = (2**(1 - j_re) * a_re * cd_R**(-0.25 - j_re/2) * d_re**(-j_re)) / gamma(j_re)
    term2_R = abs_x**(-0.5 + j_re)
    bessel_R = kv(0.5 - j_re, abs_x / np.sqrt(cd_R))
    return term1_R * term2_R * bessel_R

def numerical_FT_A2BRe(x, a_re, c_re, d_re, j_re):
    lam_grid = np.linspace(-40, 40, 4000)
    abs_lam = np.abs(lam_grid)
    # in the template, b2 is just d_re. Wait, no, d_re = 1 + d_re * b2.
    # The template computes:
    # d_re_phys = 1 + d_re_param * b2.
    # The amplitude is a_re * exp(-c_re * abs_lam) / (d_re_phys)^j_re.
    # Wait, the template has: d_re = 1.0 + fitted_params['d_re'] * b2
    # So d_re is effectively (1 + d * b^2).
    # Then the amplitude is a_re * exp(-c_re |lam|) / (d_re)^j_re.
    # This has NO lambda dependence in the denominator!
    # Ah! The Fourier transform of a_re / (d_re)^j_re * exp(-c_re |lam|) is simply:
    # (a_re / d_re^j_re) * \int d\lambda e^{ix\lambda} e^{-c_re |\lambda|}
    # = (a_re / d_re^j_re) * (2 c_re) / (c_re^2 + x^2).
    pass

# Wait, let's look at the template's analytical FT carefully!
