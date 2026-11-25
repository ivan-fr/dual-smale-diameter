"""Exact comparison of the critical-chord and radius criteria in degree ten."""
from fractions import Fraction as F
from math import prod

n = 10
radii = [F(1), F(1)] + [F(1, 3)] * 7
radius = max(radii)
chord = 2 * radius  # attained by the two real critical points +1 and -1
denominator = 4**n * n * prod(radii) * radius
chord_bound = 2 * chord**n / denominator
radius_bound = 2 * radius**n / denominator
assert chord_bound == F(2187, 5120)
assert radius_bound == F(2187, 5242880)
assert radius_bound < F(1, n) < chord_bound
assert 2 * F(11, 10)**(n - 1) / (2**n * n) < F(1, n)
print(f"degree {n}: radius bound {radius_bound}, chord bound {chord_bound}")
