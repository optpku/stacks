/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Category
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Restriction of modules to open subspaces

This file provides restriction functors for modules on a ringed space, both from the ambient
space and between nested open subspaces.  It also exposes the morphisms of restricted ringed
spaces and their functorial comparison API.
-/

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- Restriction of `𝒪_X`-modules from `X` to the open subspace `U`. -/
@[stacks 08DP "restriction to an open subspace"]
abbrev moduleRestrictionToOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    RingedSpace.Modules X ⥤ openSubspaceModuleCategory X U :=
  RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding)

/-- Restriction of cochain complexes of `𝒪_X`-modules to the open subspace `U`. -/
abbrev moduleRestrictionComplexToOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤
      CochainComplex (openSubspaceModuleCategory X U) ℤ :=
  (moduleRestrictionToOpen X U).mapHomologicalComplex (up ℤ)

/-- The cochain complex obtained by restricting `K` to the open subspace `U`. -/
abbrev restrictedComplexOnOpen
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    CochainComplex (openSubspaceModuleCategory X U) ℤ :=
  (moduleRestrictionComplexToOpen X U).obj K

/-- The open immersion of the restricted ringed space is flat. -/
theorem ofRestrict_isFlat (X : RingedSpace.{u}) (U : Opens X.carrier) :
    RingedSpace.Hom.IsFlat (X.ofRestrict U.isOpenEmbedding) := sorry

/-- Restriction to an open subspace is exact. -/
theorem OpenSubspace.Restriction.isExact
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    exactFunctor (RingedSpace.Modules X) (openSubspaceModuleCategory X U)
      (moduleRestrictionToOpen X U) := sorry

/-- Restriction to an open subspace, bundled with its exactness certificate. -/
noncomputable def OpenSubspace.Restriction.exact
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    RingedSpace.Modules X ⥤ₑ openSubspaceModuleCategory X U :=
  ⟨moduleRestrictionToOpen X U, OpenSubspace.Restriction.isExact X U⟩

/-- Restriction to an open subspace is additive on module sheaves. -/
theorem OpenSubspace.Restriction.additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleRestrictionToOpen X U).Additive := sorry

/-- Restriction to an open subspace preserves finite limits. -/
theorem OpenSubspace.Restriction.preservesFiniteLimits (X : RingedSpace.{u})
    (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleRestrictionToOpen X U) := sorry

/-- Restriction to an open subspace preserves finite colimits. -/
theorem OpenSubspace.Restriction.preservesFiniteColimits (X : RingedSpace.{u})
    (U : Opens X.carrier) :
    PreservesFiniteColimits (moduleRestrictionToOpen X U) := sorry

/-- The range of the composite from the restriction of `X` to `f ⁻¹(V)` lies in `V`. -/
theorem restrictedMorphismToOpen_range_subset
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    Set.range (((X.ofRestrict (preimageOpen f V).isOpenEmbedding).hom ≫ f.hom).base) ⊆
      Set.range ((Y.ofRestrict V.isOpenEmbedding).hom.base) := sorry

/-- The morphism of restricted ringed spaces induced by `f : X ⟶ Y` and an open subset
`V ⊆ Y`. -/
@[stacks 08DP "morphism restricted over an open subspace"]
noncomputable def restrictedMorphismToOpen
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    X.restrict (preimageOpen f V).isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding :=
  ⟨PresheafedSpace.IsOpenImmersion.lift
    (Y.ofRestrict V.isOpenEmbedding).hom
    ((X.ofRestrict (preimageOpen f V).isOpenEmbedding).hom ≫ f.hom)
    (fun _ ⟨x, hx⟩ ↦ ⟨⟨f.hom.base x.1, x.2⟩, hx⟩)⟩

/-- Restricting `f` to `f ⁻¹(V)` factors the corresponding ambient open immersions. -/
theorem restrictedMorphismToOpen_fac
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    restrictedMorphismToOpen f V ≫ Y.ofRestrict V.isOpenEmbedding =
      X.ofRestrict (preimageOpen f V).isOpenEmbedding ≫ f := sorry

/-- The range of the smaller restricted open immersion lies in the larger one. -/
theorem restrictedMorphismBetweenOpens_range_subset
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    Set.range ((X.ofRestrict W.isOpenEmbedding).hom.base) ⊆
      Set.range ((X.ofRestrict U.isOpenEmbedding).hom.base) := sorry

/-- The morphism of restricted ringed spaces induced by an inclusion of opens `W ⊆ U`. -/
@[stacks 08DP "morphism between restricted open subspaces"]
noncomputable def restrictedMorphismBetweenOpens
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    X.restrict W.isOpenEmbedding ⟶ X.restrict U.isOpenEmbedding :=
  ⟨PresheafedSpace.IsOpenImmersion.lift
    (X.ofRestrict U.isOpenEmbedding).hom
    (X.ofRestrict W.isOpenEmbedding).hom
    (fun _ ⟨w, hw⟩ ↦ ⟨⟨w.1, h w.2⟩, hw⟩)⟩

/-- The morphism `X|_W ⟶ X|_U` induced by `W ⊆ U` factors the open immersion `X|_W ⟶ X`
through `X|_U ⟶ X`. -/
theorem restrictedMorphismBetweenOpens_fac
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    restrictedMorphismBetweenOpens X h ≫ X.ofRestrict U.isOpenEmbedding =
      X.ofRestrict W.isOpenEmbedding := sorry

/-- The morphism between the restricted ringed spaces associated to nested opens is flat. -/
theorem restrictedMorphismBetweenOpens_isFlat (X : RingedSpace.{u})
    {W U : Opens X.carrier} (h : W ≤ U) :
    RingedSpace.Hom.IsFlat (restrictedMorphismBetweenOpens X h) := sorry

/-- Restriction of `𝒪_U`-modules from `U` to the smaller open subspace `W ⊆ U`. -/
@[stacks 08DP "restriction between open subspaces"]
abbrev moduleRestrictionBetweenOpens
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    openSubspaceModuleCategory X U ⥤ openSubspaceModuleCategory X W :=
  RingedSpace.Hom.pullback (restrictedMorphismBetweenOpens X h)

/-- Restriction between nested open subspaces is exact on module sheaves. -/
theorem OpenSubspace.Restriction.betweenIsExact
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    exactFunctor (openSubspaceModuleCategory X U) (openSubspaceModuleCategory X W)
      (moduleRestrictionBetweenOpens X h) := sorry

/-- Restriction between nested open subspaces, bundled with its exactness certificate. -/
noncomputable def OpenSubspace.Restriction.betweenExact
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    openSubspaceModuleCategory X U ⥤ₑ openSubspaceModuleCategory X W :=
  ⟨moduleRestrictionBetweenOpens X h, OpenSubspace.Restriction.betweenIsExact X h⟩

/-- The canonical isomorphism identifying direct restriction from `X` with iterated restriction
through an intermediate open. -/
@[stacks 08DP "composition isomorphism for restrictions to open subspaces"]
noncomputable def OpenSubspace.Restriction.compIso
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    moduleRestrictionToOpen X U ⋙ moduleRestrictionBetweenOpens X h ≅
      moduleRestrictionToOpen X W :=
  (RingedSpace.Hom.pullbackCompIso
      (restrictedMorphismBetweenOpens X h) (X.ofRestrict U.isOpenEmbedding)).symm ≪≫
    eqToIso (congrArg RingedSpace.Hom.pullback
      (InducedCategory.hom_ext
        (PresheafedSpace.IsOpenImmersion.lift_fac (X.ofRestrict U.isOpenEmbedding).hom
          (X.ofRestrict W.isOpenEmbedding).hom
          (fun _ ⟨w, hw⟩ ↦ ⟨⟨w.1, h w.2⟩, hw⟩))))

/-- Iterated restriction through nested opens `T ⊆ W ⊆ U` is canonically isomorphic to direct
restriction from `U` to `T`. -/
@[stacks 08DP "composition of restrictions between open subspaces"]
noncomputable def OpenSubspace.Restriction.betweenCompIso
    (X : RingedSpace.{u}) {T W U : Opens X.carrier}
    (hTW : T ≤ W) (hWU : W ≤ U) :
    moduleRestrictionBetweenOpens X hWU ⋙ moduleRestrictionBetweenOpens X hTW ≅
      moduleRestrictionBetweenOpens X (hTW.trans hWU) :=
  (RingedSpace.Hom.pullbackCompIso (restrictedMorphismBetweenOpens X hTW)
      (restrictedMorphismBetweenOpens X hWU)).symm ≪≫
    eqToIso (congrArg RingedSpace.Hom.pullback
      (InducedCategory.hom_ext
        (PresheafedSpace.IsOpenImmersion.lift_uniq (X.ofRestrict U.isOpenEmbedding).hom
          (X.ofRestrict T.isOpenEmbedding).hom
          (fun _ ⟨t, ht⟩ ↦ ⟨⟨t.1, (hTW.trans hWU) t.2⟩, ht⟩)
          ((restrictedMorphismBetweenOpens X hTW).hom ≫
            (restrictedMorphismBetweenOpens X hWU).hom)
          ((Category.assoc _ _ _).trans
            ((congrArg
                (fun k ↦ (restrictedMorphismBetweenOpens X hTW).hom ≫ k)
                (PresheafedSpace.IsOpenImmersion.lift_fac (X.ofRestrict U.isOpenEmbedding).hom
                  (X.ofRestrict W.isOpenEmbedding).hom
                  (fun _ ⟨w, hw⟩ ↦ ⟨⟨w.1, hWU w.2⟩, hw⟩))).trans
              (PresheafedSpace.IsOpenImmersion.lift_fac (X.ofRestrict W.isOpenEmbedding).hom
                (X.ofRestrict T.isOpenEmbedding).hom
                (fun _ ⟨t, ht⟩ ↦ ⟨⟨t.1, hTW t.2⟩, ht⟩)))))))

end AlgebraicGeometry.RingedSpace
