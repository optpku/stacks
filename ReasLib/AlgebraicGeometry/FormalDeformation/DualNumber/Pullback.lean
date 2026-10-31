/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.MvRatFunc.Frobenius
public import ReasLib.RingTheory.DualNumber.Derivation
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Section
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Derivation

/-!
# Derivation sections and a nonsurjective dual-number pullback

Relative derivations give residue-compatible morphisms into dual numbers.
A rational-function partial derivative yields a pullback whose first projection
does not surject onto the residue field.
-/

@[expose] public section

open CategoryTheory TrivSqZeroExt
open scoped DualNumber

universe u

namespace ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- A relative derivation defines a morphism from the residue-field object to
the dual-number object. -/
@[deprecated derivationToDualNumber (since := "2026-10-22")]
abbrev homOfDerivation (D : Derivation Λ k k) : residue Λ k ⟶ dualNumber Λ k :=
  derivationToDualNumber D

/-- The underlying map of the derivation morphism is its dual-number algebra map. -/
theorem homOfDerivation_hom (D : Derivation Λ k k) :
    (homOfDerivation D).hom = D.toDualNumberAlgHom := rfl

/-- The derivation morphism sends `a` to `inl a + inr (D a)`. -/
theorem homOfDerivation_apply (D : Derivation Λ k k) (value : k) :
    (homOfDerivation D).hom value = inl value + inr (D value) :=
  derivationToDualNumber_apply D value

open MvRatFunc.Frobenius

/-- The first projection of the algebra pullback of the first rational-function
partial-derivative section and the constant section is not surjective. -/
theorem not_surjective_algebraPullback_toResidue (n p : ℕ) [Fact p.Prime] [NeZero n] :
    ¬ Function.Surjective
      (AlgHom.pullbackFst (pderiv n p 0).toDualNumberAlgHom
        (inlAlgHom (baseField n p) (functionField n p) (functionField n p))) := sorry

end ArtinianLocalAlgCat
