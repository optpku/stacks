module

public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cohomology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Right-Derived Spectral-Sequence Realizations

This file specializes the neutral filtered realization with a functorial abutment to bounded-
below total right-derived functors.  The filtered complex, spectral sequence, association, and
abutment comparison remain owned by the neutral realization API.
-/

@[expose] public section

open CategoryTheory
noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} B]

/-- The cohomological abutment of the bounded-below total right-derived value of `T` at `K`,
computed with the localization model `Q`. -/
@[stacks 015X "derived-functor spectral-sequence abutment"]
noncomputable abbrev abutment
    (T : A ⥤ B) [T.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) (n : ℤ) : B :=
  Functor.RightDerived.Bounded.cohomology T Q K n

/-- The degree-`n` derived abutment as a functor of the bounded-below complex. -/
@[stacks 015X "functorial derived-functor spectral-sequence abutment"]
noncomputable abbrev abutmentFunctor
    (T : A ⥤ B) [T.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℤ) : CochainComplex.Plus A ⥤ B :=
  Functor.RightDerived.Bounded.cohomologyFunctor T Q n

/-- Evaluation of `abutmentFunctor` recovers the derived abutment. -/
@[simp, stacks 015X "functorial derived-functor spectral-sequence abutment"]
theorem abutmentFunctor_obj
    (T : A ⥤ B) [T.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℤ) (K : CochainComplex.Plus A) :
    (abutmentFunctor T Q n).obj K = abutment T Q K n := sorry

/-- The morphism of degree-`n` derived abutments induced by a cochain map. -/
@[stacks 015X "functorial derived-functor spectral-sequence abutment"]
noncomputable abbrev abutmentMap
    (T : A ⥤ B) [T.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {K L : CochainComplex.Plus A} (f : K ⟶ L) (n : ℤ) :
    abutment T Q K n ⟶ abutment T Q L n :=
  Functor.RightDerived.Bounded.cohomologyMap T Q f n

/-- The action of `abutmentFunctor` on a cochain map is the canonical abutment map. -/
@[simp, stacks 015X "functorial derived-functor spectral-sequence abutment"]
theorem abutmentFunctor_map
    (T : A ⥤ B) [T.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℤ) {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (abutmentFunctor T Q n).map f = abutmentMap T Q f n := sorry

/-- The abutment map induced by an identity cochain map is the identity. -/
@[simp, stacks 015X "identity derived-functor spectral-sequence abutment map"]
theorem abutmentMap_id
    (T : A ⥤ B) [T.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) (n : ℤ) :
    abutmentMap T Q (𝟙 K) n = 𝟙 (abutment T Q K n) := sorry

/-- Abutment maps preserve composition of cochain maps. -/
@[simp, reassoc, stacks 015X "composition of derived-functor spectral-sequence abutment maps"]
theorem abutmentMap_comp
    (T : A ⥤ B) [T.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {K L M : CochainComplex.Plus A} (f : K ⟶ L) (g : L ⟶ M) (n : ℤ) :
    abutmentMap T Q (f ≫ g) n =
      abutmentMap T Q f n ≫ abutmentMap T Q g n := sorry

/-- A bounded, convergent filtered realization whose functorial abutment is the total right
derived value of `T` at `K` computed with `Q`. -/
@[stacks 015X "derived-functor spectral-sequence realization"]
noncomputable abbrev Realization
    (T : A ⥤ B) [T.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) :=
  FilteredComplex.SpectralSequence.Realization.WithAbutment
    (fun n => abutmentFunctor T Q n) K

namespace Realization

variable (T : A ⥤ B) [T.Additive]
  {E : Type u₃} [Category.{v₃} E]
  (Q : HomotopyCategory.Plus A ⥤ E)
  [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
  [T.toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso A)]

/-- The generic filtered realization underlying a right-derived realization. -/
@[stacks 015X "underlying filtered derived-functor realization"]
noncomputable abbrev toFilteredRealization {K : CochainComplex.Plus A}
    (S : Realization T Q K) :
    FilteredComplex.SpectralSequence.Realization (C := B) :=
  S.toRealization

/-- Forgetting the abutment comparison retains the filtered complex. -/
@[simp, stacks 015X "underlying filtered derived-functor realization"]
theorem toFilteredRealization_filtered {K : CochainComplex.Plus A}
    (S : Realization T Q K) : S.toFilteredRealization.filtered = S.filtered := sorry

/-- Forgetting the abutment comparison retains the spectral sequence. -/
@[simp, stacks 015X "underlying filtered derived-functor realization"]
theorem toFilteredRealization_sequence {K : CochainComplex.Plus A}
    (S : Realization T Q K) : S.toFilteredRealization.sequence = S.sequence := sorry

/-- Forgetting the abutment comparison retains the chosen association. -/
@[simp, stacks 015X "underlying filtered derived-functor realization"]
theorem toFilteredRealization_association {K : CochainComplex.Plus A}
    (S : Realization T Q K) : S.toFilteredRealization.association = S.association := sorry

end Realization

end CategoryTheory.Functor.RightDerived.SpectralSequence
