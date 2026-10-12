/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AffinePlaneInt

/-- The affine plane `Spec (CommRingCat.of (MvPolynomial (Fin 2) ℤ))`. -/
abbrev affinePlaneInt : Scheme :=
  Spec (CommRingCat.of (MvPolynomial (Fin 2) ℤ))

/-- The global section of `affinePlaneInt` corresponding to the coordinate
`x = MvPolynomial.X 0`. -/
abbrev coordX : Γ(affinePlaneInt, ⊤) :=
  (Scheme.ΓSpecIso _).inv (MvPolynomial.X (0 : Fin 2))

/-- There is a module on the integer affine plane with a global section whose
restriction to the basic open defined by `coordX` vanishes, while no power of
`coordX` annihilates that section. -/
theorem exists_section_not_pow_smul_eq_zero_of_isZero_restrict :
    ∃ (F : affinePlaneInt.Modules) (s : Γ(F, ⊤)),
      IsZero (F.restrict (affinePlaneInt.basicOpen coordX).ι) ∧
        ∀ n : ℕ, coordX ^ n • s ≠ 0 := sorry

end AlgebraicGeometry.AffinePlaneInt
