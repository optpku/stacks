/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.DerivedResolutionComparison
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe w

namespace ActualResolutionComparison
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
variable [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

/-- The single-object coefficient map has identity component in degree zero. -/
def singleCoefficientMap (M : C) :
    (CochainComplex.single₀ D).obj (F.obj M) ⟶
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ C).obj M) :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨𝟙 _, by
    change 𝟙 _ ≫ F.map (0 : _ ⟶ _) = 0
    rw [F.map_zero, comp_zero]⟩

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] in
/-- The coefficient map is the inverse of the canonical single-complex comparison. -/
theorem singleCoefficientMap_eq (M : C) :
    singleCoefficientMap F M =
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).app M).inv := by
  apply HomologicalComplex.from_single_hom_ext
  change (singleCoefficientMap F M).f 0 =
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv.app M).f 0
  simp only [singleCoefficientMap, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
  change 𝟙 (F.obj M) = 𝟙 (F.obj M) ≫ F.map (𝟙 M)
  rw [F.map_id, Category.comp_id]

instance singleCoefficientMap_isIso (M : C) : IsIso (singleCoefficientMap F M) := by
  rw [singleCoefficientMap_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
omit [EnoughInjectives C] in
/-- Exactness inverts the bounded-below quasi-isomorphisms before derivation. -/
theorem exactToBoundedBelowDerived_inverts
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (HomotopyCategory.Plus.quasiIso C).IsInvertedBy F.toBoundedBelowDerived := by
  intro K L f hf
  haveI : IsIso (DerivedCategory.Qh.map f.hom) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      f.hom hf
  haveI : IsIso ((DerivedCategory.Qh ⋙ F.mapDerivedCategory).map f.hom) := by
    change IsIso (F.mapDerivedCategory.map (DerivedCategory.Qh.map f.hom))
    infer_instance
  have hIso : IsIso (((HomotopyCategory.Plus.ι C) ⋙ Functor.Homotopy.toDerived F).map f) := by
    change IsIso ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map f.hom)
    rw [← NatIso.naturality_2 F.mapDerivedCategoryFactorsh.symm f.hom]
    infer_instance
  haveI : IsIso (DerivedCategory.Plus.ι.map (F.toBoundedBelowDerived.map f)) :=
    hIso
  exact isIso_of_reflects_iso (F.toBoundedBelowDerived.map f)
    (DerivedCategory.Plus.ι : DerivedCategory.Plus D ⥤ DerivedCategory D)

/-- The actual derived unit on a coefficient in degree zero, constructed from
the single-object map, extension comparison, and bounded-derived unit. -/
def underivedToDerived (M : C) : singleModel (F.obj M) ⟶
    (Functor.RightDerived.Bounded.functor F).obj (singleModel M) :=
  DerivedCategory.Plus.Q.map ((CochainComplex.Plus.extendNat D).map (singleCoefficientMap F M)) ≫
    Functor.RightDerived.Bounded.fromCochainMap F
      (ObjectProperty.homMk (ComplexShape.embeddingUpNat.mapAppIso F
        ((CochainComplex.single₀ C).obj M)).inv)

set_option backward.isDefEq.respectTransparency false in
/-- Exact functors have invertible derived units on degree-zero objects. -/
instance underivedToDerived_isIso [PreservesFiniteLimits F] [PreservesFiniteColimits F] (M : C) :
    IsIso (underivedToDerived F M) := by
  haveI : IsIso (Functor.RightDerived.Bounded.unit F) :=
    Functor.isIso_of_isRightDerivedFunctor_of_inverts
      (Functor.RightDerived.Bounded.functor F) (Functor.RightDerived.Bounded.unit F)
      (exactToBoundedBelowDerived_inverts F)
  unfold underivedToDerived Functor.RightDerived.Bounded.fromCochainMap
  haveI : IsIso (ObjectProperty.homMk (ComplexShape.embeddingUpNat.mapAppIso F
      ((CochainComplex.single₀ C).obj M)).inv :
      (CochainComplex.Plus.extendNat D).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ C).obj M)) ⟶
      F.mapCochainComplexPlus.obj
        ((CochainComplex.Plus.extendNat C).obj ((CochainComplex.single₀ C).obj M))) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    change IsIso (ComplexShape.embeddingUpNat.mapAppIso F
      ((CochainComplex.single₀ C).obj M)).inv
    infer_instance
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_))
  · infer_instance
  · infer_instance
  · infer_instance
  · exact ((asIso (Functor.RightDerived.Bounded.unit F)).app _).isIso_hom

/-- The exact-functor comparison inverts only the specified single-object derived unit. -/
def exactUnitIso [PreservesFiniteLimits F] [PreservesFiniteColimits F] (M : C) :=
  @asIso _ _ _ _ (underivedToDerived F M) (underivedToDerived_isIso F M)

end ActualResolutionComparison
