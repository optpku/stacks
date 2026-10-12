/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Compact
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import ReasLib.CategoryTheory.Pretriangulated.Tilting

/-!
# Tilting Objects for Derived Categories of Modules

This file packages the intrinsic ordinary-algebra form of the derived Morita criterion.  The
tilting predicate is independent of any chosen equivalence or bimodule realization, so its four
constituent conditions can be reused separately.
-/

@[expose] public section

noncomputable section

universe uR uA uB

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra

namespace DerivedCategory.Morita

variable {R : Type uR} [CommRing R]

/-- A tilting object for the `R`-algebra `A` in `D(B)` is a compact weak generator with no
nonzero self-extensions and with degree-zero endomorphism algebra `A`. -/
@[stacks 09SC "tilting object for ordinary derived Morita theory"]
abbrev IsTiltingFor (R : Type uR) [CommRing R]
    (A : Type uA) [Ring A] [Algebra R A]
    {B : Type uB} [Ring B] [Algebra R B]
    (P : DerivedCategory (ModuleCat (Bᵐᵒᵖ))) : Prop :=
  CategoryTheory.IsTiltingFor (R := R) (E := A) P

/-- The compactness, weak-generation, self-extension, and endomorphism-algebra characterization
of an ordinary tilting object. -/
@[stacks 09SC "intrinsic tilting criterion"]
theorem isTiltingFor_iff
    (A : Type uA) [Ring A] [Algebra R A]
    {B : Type uB} [Ring B] [Algebra R B]
    (P : DerivedCategory (ModuleCat (Bᵐᵒᵖ))) :
    IsTiltingFor R A P ↔
      IsCompactObject P ∧
        IsWeakGenerator P ∧
        (∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0) ∧
        Nonempty (End P ≃ₐ[R] A) := sorry

/-- The perfect-complex characterization of an ordinary tilting object. -/
@[stacks 09SC "perfect-complex tilting criterion"]
theorem isTiltingFor_iff_isPerfect
    (A : Type uA) [Ring A] [Algebra R A]
    {B : Type uB} [Ring B] [Algebra R B]
    (P : DerivedCategory (ModuleCat (Bᵐᵒᵖ))) :
    IsTiltingFor R A P ↔
      P.IsPerfect ∧
        IsWeakGenerator P ∧
        (∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0) ∧
        Nonempty (End P ≃ₐ[R] A) := sorry

/-- An ordinary tilting object is compact. -/
@[stacks 09SC "compactness of a tilting object"]
theorem IsTiltingFor.isCompact
    {A : Type uA} [Ring A] [Algebra R A]
    {B : Type uB} [Ring B] [Algebra R B]
    {P : DerivedCategory (ModuleCat (Bᵐᵒᵖ))} (hP : IsTiltingFor R A P) :
    IsCompactObject P := sorry

/-- An ordinary tilting object is perfect. -/
@[stacks 09SC "perfectness of a tilting object"]
theorem IsTiltingFor.isPerfect
    {A : Type uA} [Ring A] [Algebra R A]
    {B : Type uB} [Ring B] [Algebra R B]
    {P : DerivedCategory (ModuleCat (Bᵐᵒᵖ))} (hP : IsTiltingFor R A P) :
    P.IsPerfect := sorry

/-- An ordinary tilting object weakly generates its derived category. -/
@[stacks 09SC "weak generation by a tilting object"]
theorem IsTiltingFor.isWeakGenerator
    {A : Type uA} [Ring A] [Algebra R A]
    {B : Type uB} [Ring B] [Algebra R B]
    {P : DerivedCategory (ModuleCat (Bᵐᵒᵖ))} (hP : IsTiltingFor R A P) :
    IsWeakGenerator P := sorry

/-- An ordinary tilting object is self-orthogonal. -/
@[stacks 09SC "self-orthogonality of a tilting object"]
theorem IsTiltingFor.isSelfOrthogonal
    {A : Type uA} [Ring A] [Algebra R A]
    {B : Type uB} [Ring B] [Algebra R B]
    {P : DerivedCategory (ModuleCat (Bᵐᵒᵖ))} (hP : IsTiltingFor R A P) :
    CategoryTheory.IsSelfOrthogonal P := sorry

/-- An ordinary tilting object has no self-extensions in nonzero degrees. -/
@[stacks 09SC "vanishing self-extensions of a tilting object"]
theorem IsTiltingFor.selfExt_eq_zero
    {A : Type uA} [Ring A] [Algebra R A]
    {B : Type uB} [Ring B] [Algebra R B]
    {P : DerivedCategory (ModuleCat (Bᵐᵒᵖ))} (hP : IsTiltingFor R A P)
    (i : ℤ) (hi : i ≠ 0) (f : P ⟶ P⟦i⟧) :
    f = 0 := sorry

/-- The endomorphism algebra of an ordinary tilting object is the prescribed source algebra. -/
@[stacks 09SC "endomorphism algebra of a tilting object"]
theorem IsTiltingFor.nonempty_endEquiv
    {A : Type uA} [Ring A] [Algebra R A]
    {B : Type uB} [Ring B] [Algebra R B]
    {P : DerivedCategory (ModuleCat (Bᵐᵒᵖ))} (hP : IsTiltingFor R A P) :
    Nonempty (End P ≃ₐ[R] A) := sorry

/-- Lemma 22.37.8 (1) (09SC): the derived categories of two `R`-algebras are `R`-linearly
triangulated-equivalent exactly when the target contains a tilting object for the source. -/
@[stacks 09SC]
theorem nonempty_equivalence_iff_exists_tilting
    {A : Type uA} [Ring A] [Algebra R A]
    {B : Type uB} [Ring B] [Algebra R B] :
    Nonempty (RLinear.TriangulatedEquivalence R
      (DerivedCategory (ModuleCat (Aᵐᵒᵖ)))
      (DerivedCategory (ModuleCat (Bᵐᵒᵖ)))) ↔
      ∃ P : DerivedCategory (ModuleCat (Bᵐᵒᵖ)), IsTiltingFor R A P := sorry

end DerivedCategory.Morita
