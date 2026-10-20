module

public import ReasLib.Algebra.Module.Length.Cyclic
import StacksCheckRecall

/- Exercise 111.9.3 (1): compute the length of `ℤ/120ℤ` over `ℤ`. -/
@[stacks 076G] #check (Module.intMod120_length :
    Module.length ℤ (ℤ ⧸ Ideal.span {(120 : ℤ)}) = (5 : ℕ∞))

/- Exercise 111.9.3 (2): compute the length of `ℂ[X]/(X^100 + X + 1)` over `ℂ[X]`. -/
@[stacks 076G] #check (Module.complexPolyMod_length :
    Module.length (Polynomial ℂ)
      (Polynomial ℂ ⧸ Ideal.span {(Polynomial.X ^ 100 + Polynomial.X + 1 : Polynomial ℂ)}) =
        (100 : ℕ∞))

/- Exercise 111.9.3 (3): compute the length of `ℝ[X]/(X^4 + 2X^2 + 1)` over `ℝ[X]`. -/
@[stacks 076G] #check (Module.realPolyMod_length :
    Module.length (Polynomial ℝ)
      (Polynomial ℝ ⧸ Ideal.span {(Polynomial.X ^ 4 + 2 * Polynomial.X ^ 2 + 1 : Polynomial ℝ)}) =
        (2 : ℕ∞))
