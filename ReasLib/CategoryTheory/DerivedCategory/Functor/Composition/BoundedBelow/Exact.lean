/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow
public import ReasLib.CategoryTheory.Functor.Derived.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition with an exact second functor

For bounded-below right-derived functors, the canonical comparison
`R(F ⋙ G) ⟶ RF ⋙ RG` is invertible when the second functor `G` is exact.  The instance in this
leaf makes that canonical fact available without rebuilding local comparison instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB wC vA vB vC uA uB uC

namespace CategoryTheory.Functor.RightDerived.Composition.BoundedBelow

-- Prefer Mathlib's proved injective derivability structure to the deferred exact-functor
-- existence instance when selecting the canonical right-derived functors in this proof.
attribute [local instance 2000] Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wC} C]

set_option backward.isDefEq.respectTransparency false in
/-- If the second functor is exact, the bounded-below right-derived composition comparison is
an isomorphism. -/
@[stacks 015M "exact second functor"]
noncomputable instance comparisonIsIsoOfSecondExact
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [EnoughInjectives A] [EnoughInjectives B]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    IsIso (comparison F G) := by
  have hG : (HomotopyCategory.Plus.quasiIso B).IsInvertedBy
      G.toBoundedBelowDerived := by
    intro K L f hf
    have : IsIso (DerivedCategory.Plus.ι.map (G.toBoundedBelowDerived.map f)) := by
      change IsIso ((Functor.Homotopy.toDerived G).map f.hom)
      exact (Functor.RightDerived.Exact.isInvertedBy G) _ hf
    exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  letI hunitG : IsIso (Functor.RightDerived.Bounded.unit G) :=
    Functor.isIso_of_isRightDerivedFunctor_of_inverts
      (Functor.RightDerived.Bounded.functor G) (Functor.RightDerived.Bounded.unit G) hG
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨Y, ⟨e⟩⟩ :=
    Functor.EssSurj.mem_essImage ((InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙
      (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)) K
  rw [← NatTrans.isIso_app_iff_of_iso (comparison F G) e]
  let J := (InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Y
  change IsIso ((comparison F G).app (DerivedCategory.Plus.Qh.obj J))
  letI (n : ℤ) : Injective (J.obj.as.X n) := by dsimp [J]; infer_instance
  letI : IsIso ((Functor.RightDerived.Bounded.unit F).app J) := by
    dsimp only [Functor.RightDerived.Bounded.unit, Functor.RightDerived.Bounded.functor]
    infer_instance
  letI : IsIso ((Functor.RightDerived.Bounded.unit (F ⋙ G)).app J) := by
    dsimp only [Functor.RightDerived.Bounded.unit, Functor.RightDerived.Bounded.functor]
    infer_instance
  have hfac :
      (Functor.RightDerived.Bounded.unit (F ⋙ G)).app J ≫
        (comparison F G).app (DerivedCategory.Plus.Qh.obj J) =
      (Functor.toBoundedBelowDerived.compIso F G).hom.app J ≫
        (Functor.RightDerived.Bounded.unit G).app (F.mapHomotopyCategoryPlus.obj J) ≫
        (Functor.RightDerived.Bounded.functor G).map
          ((Functor.RightDerived.Bounded.unit F).app J) := by
    simp only [comparison, Functor.RightDerived.Composition.Localization.comparison,
      Functor.rightDerived_fac_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.comp_id]
    erw [Category.id_comp]
  letI : IsIso ((Functor.RightDerived.Bounded.unit (F ⋙ G)).app J ≫
      (comparison F G).app (DerivedCategory.Plus.Qh.obj J)) := by
    rw [hfac]
    exact IsIso.comp_isIso'
      ((Functor.toBoundedBelowDerived.compIso F G).app J).isIso_hom
      (IsIso.comp_isIso'
        (NatIso.isIso_app_of_isIso (Functor.RightDerived.Bounded.unit G) _)
        (Functor.map_isIso _ _))
  exact IsIso.of_isIso_comp_left
    ((Functor.RightDerived.Bounded.unit (F ⋙ G)).app J) _

end CategoryTheory.Functor.RightDerived.Composition.BoundedBelow
