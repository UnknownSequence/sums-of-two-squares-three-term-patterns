"""Exponents of Table 1 of the note, in exact arithmetic."""
from fractions import Fraction as Fr
def old_a(t): return (1 - 2 * t) / (10 - 12 * t)
def old_b(t): return (1 - 2 * t) / (10 - 8 * t)
def new_a(t): return (1 - 2 * t) / (8 - 8 * t)
def new_b(t): return (1 - 2 * t) / (8 - 4 * t)
for name, t in [("Selberg 1/4", Fr(1, 4)), ("Kim-Sarnak 7/64", Fr(7, 64)), ("Selberg conj. 0", Fr(0))]:
    print(f"{name:16s} old(a)={old_a(t)} ({float(old_a(t)):.4f})  new(a)={new_a(t)} ({float(new_a(t)):.4f})  "
          f"old(b)={old_b(t)} ({float(old_b(t)):.4f})  new(b)={new_b(t)} ({float(new_b(t)):.4f})")
