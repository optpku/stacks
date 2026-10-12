/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import stacks_project.Chap69.Lemma_69_20_1_ProjectiveSpace
public import stacks_project.Chap69.Lemma_69_20_1_Twist
public import stacks_project.Chap108.Lemma_108_5_10_Hilbert

/-!
# Hilbert Quot of finite free sheaves on projective space over `Spec(ℤ)`

The source specialization of `quotHilbert` to `𝒪^{⊕ r}` on `P^n` over
`Spec(ℤ)`, with `𝒪(1)` as the twisting sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- `Spec(ℤ)` as an algebraic space over itself. -/
abbrev specSpace : AlgebraicSpace (⊤_ Scheme.{u}) :=
  ofOver (Over.mk (𝟙 (⊤_ Scheme.{u})))

/-- `specSpace` is `ofOver` of the identity of the terminal scheme. -/
theorem specSpace_eq :
    specSpace = ofOver (Over.mk (𝟙 (⊤_ Scheme.{u}))) :=
  sorry

/-- The structure morphism `P^n_ℤ ⟶ Spec(ℤ)` is of finite presentation. -/
instance instFinitePresentation_projectiveToSpec (n : ℕ) :
    FinitePresentation (ProjectiveSpace.toBase n specSpace) :=
  sorry

/-- The structure morphism `P^n_ℤ ⟶ Spec(ℤ)` is separated. -/
instance instSeparated_projectiveToSpec (n : ℕ) :
    Separated (ProjectiveSpace.toBase n specSpace) :=
  sorry

/-- The finite free sheaf `𝒪^{⊕ r}` on `P^n_ℤ` is quasi-coherent. -/
instance instIsQuasicoherent_freeFin (n r : ℕ) :
    (SheafOfModules.freeFin r :
      (ProjectiveSpace n specSpace).Modules).IsQuasicoherent :=
  sorry

/-- The Hilbert Quot functor of quotients of `𝒪_{P^n_ℤ}^{⊕ r}` with Hilbert
polynomial `P`. -/
abbrev quotHilbert_projective (n r : ℕ) (P : ℤ → ℤ) :=
  quotHilbert (ProjectiveSpace.toBase n specSpace)
    (SheafOfModules.freeFin r : (ProjectiveSpace n specSpace).Modules)
    (ProjectiveSpace.twistingSheaf n specSpace) P

/-- `quotHilbert_projective` is `quotHilbert` of the structure morphism of
`P^n_ℤ`, the finite free sheaf of rank `r`, and `𝒪(1)`. -/
theorem quotHilbert_projective_eq (n r : ℕ) (P : ℤ → ℤ) :
    quotHilbert_projective n r P =
      quotHilbert (ProjectiveSpace.toBase n specSpace)
        (SheafOfModules.freeFin r : (ProjectiveSpace n specSpace).Modules)
        (ProjectiveSpace.twistingSheaf n specSpace) P :=
  sorry

/-- The integer-valued function associated to a rational polynomial that takes
integer values at integers, extracted from numerators. -/
def ofIntegerValued (P : Polynomial ℚ)
    (hP : ∀ k : ℤ, (P.eval (k : ℚ)).den = 1) : ℤ → ℤ :=
  fun k ↦
    let _ := hP k
    (P.eval (k : ℚ)).num

/-- Evaluating `ofIntegerValued P hP` recovers the original rational polynomial
at integer arguments. -/
theorem ofIntegerValued_eval (P : Polynomial ℚ)
    (hP : ∀ k : ℤ, (P.eval (k : ℚ)).den = 1) (k : ℤ) :
    (ofIntegerValued P hP k : ℚ) = P.eval (k : ℚ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
