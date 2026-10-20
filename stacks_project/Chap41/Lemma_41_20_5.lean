/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Henselian

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 41.20.5: a quasi-compact separated étale scheme over a henselian pair
decomposes uniquely into complementary open subschemes, one finite over the base and one with
empty special fibre. -/
@[stacks 0BTN] #check
  (AlgebraicGeometry.Scheme.Hom.exists_clopen_decomposition_of_henselianPair :
    {A : Type u} → [CommRing A] → (I : Ideal A) → [HenselianRing A I] →
      {U : Scheme.{u}} → (f : U ⟶ Spec (CommRingCat.of A)) →
      [QuasiCompact f] → [IsSeparated f] → [Etale f] →
      [IsFinite (pullback.snd f (Spec.quotientMap I))] →
      ∃ Ufin Uaway : U.Opens,
        IsCompl Ufin Uaway ∧ IsFinite (Ufin.ι ≫ f) ∧
          IsEmpty (pullback (Uaway.ι ≫ f) (Spec.quotientMap I) : Scheme))

#check
  (AlgebraicGeometry.Scheme.Hom.clopen_decomposition_unique_of_henselianPair :
    {A : Type u} → [CommRing A] → (I : Ideal A) → [HenselianRing A I] →
      {U : Scheme.{u}} → (f : U ⟶ Spec (CommRingCat.of A)) →
      [QuasiCompact f] → [IsSeparated f] → [Etale f] →
      [IsFinite (pullback.snd f (Spec.quotientMap I))] →
      {Ufin Uaway Vfin Vaway : U.Opens} →
      (IsCompl Ufin Uaway ∧ IsFinite (Ufin.ι ≫ f) ∧
        IsEmpty (pullback (Uaway.ι ≫ f) (Spec.quotientMap I) : Scheme)) →
      (IsCompl Vfin Vaway ∧ IsFinite (Vfin.ι ≫ f) ∧
        IsEmpty (pullback (Vaway.ι ≫ f) (Spec.quotientMap I) : Scheme)) →
      Ufin = Vfin ∧ Uaway = Vaway)
