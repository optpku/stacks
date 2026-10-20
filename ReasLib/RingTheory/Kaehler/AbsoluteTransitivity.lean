module

public import ReasLib.Algebra.Category.ModuleCat.ShortComplex
public import ReasLib.RingTheory.Kaehler.BaseChange

/-!
# Base-Changed Absolute Transitivity for Kähler Differentials

This module packages the absolute Kähler transitivity row after extension of
scalars and records its exactness for polynomial algebras.
-/

@[expose] public section

open CategoryTheory
open scoped KaehlerDifferential TensorProduct

noncomputable section

universe u

namespace KaehlerDifferential.AbsoluteTransitivity

variable (A P B : Type u)
variable [CommRing A] [CommRing P] [CommRing B]
variable [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]

/-- The two maps in the absolute Kähler transitivity row remain a complex after
base change from `P` to `B`. -/
theorem maps_comp :
    ((KaehlerDifferential.map ℤ A P P).baseChange B).comp
        (KaehlerDifferential.tensorMapBaseChange ℤ A P B) = 0 := sorry

/-- The base change to `B` of the absolute Kähler transitivity row
`Ω[A⁄ℤ] ⟶ Ω[P⁄ℤ] ⟶ Ω[P⁄A]`. -/
noncomputable def complex : ShortComplex (ModuleCat.{u} B) :=
  ShortComplex.moduleCatMk
    (KaehlerDifferential.tensorMapBaseChange ℤ A P B)
    ((KaehlerDifferential.map ℤ A P P).baseChange B)
    (maps_comp A P B)

/-- The absolute Kähler transitivity row of a polynomial algebra remains short exact
after arbitrary base change. -/
theorem shortExact_mvPolynomial (n : ℕ)
    [Algebra (MvPolynomial (Fin n) A) B]
    [IsScalarTower A (MvPolynomial (Fin n) A) B] :
    (complex A (MvPolynomial (Fin n) A) B).ShortExact := sorry

/-- Freeness of the relative differential term is visible through the third object of
the absolute transitivity complex. -/
instance complexX3Free [hfree : Module.Free B (B ⊗[P] Ω[P⁄A])] :
    Module.Free B (complex A P B).X₃ := sorry

/-- Finiteness of the relative differential term is visible through the third object of
the absolute transitivity complex. -/
instance complexX3Finite [hfinite : Module.Finite B (B ⊗[P] Ω[P⁄A])] :
    Module.Finite B (complex A P B).X₃ := sorry

end KaehlerDifferential.AbsoluteTransitivity
