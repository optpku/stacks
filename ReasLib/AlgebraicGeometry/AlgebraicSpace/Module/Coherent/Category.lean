/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Coherent module sheaves on the small étale presentation site

This is the full subcategory of coherent objects in `AlgebraicSpace.Modules`, with its
canonical inclusion. Coherence is the ringed-site predicate; the slice sheafification
instances are the prerequisites for that predicate. The source specialization to locally
Noetherian spaces is Definition 69.12.1, Stacks Tag 07UA.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Abelian-group-valued weak sheafification exists on every double slice of the small étale
topology of an algebraic space. -/
instance smallEtaleTopology_over_over_hasWeakSheafify {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ (U : smallEtaleSite X) (V : Over U),
      HasWeakSheafify (((smallEtaleTopology X).over U).over V) AddCommGrpCat.{u} :=
  fun U V ↦ by
    -- Local instance justification (defeq pin): Use the specified atlas-based single-slice
    -- reflector and defer only its finite-limit-preservation law before transporting it.
    letI : HasSheafify ((smallEtaleTopology X).over V.left) AddCommGrpCat.{u} :=
      { isRightAdjoint := smallEtaleOverAbelianSheafification X V.left
        isLeftExact := by sorry }
    exact (V.iteratedSliceEquiv.hasSheafify (((smallEtaleTopology X).over U).over V)
      ((smallEtaleTopology X).over V.left) AddCommGrpCat.{u}).isRightAdjoint

/-- On every double slice of the small étale topology of an algebraic space, sheafification
equivalences are the locally bijective morphisms. -/
instance smallEtaleTopology_over_over_wEqualsLocallyBijective {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ (U : smallEtaleSite X) (V : Over U),
      (((smallEtaleTopology X).over U).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- The category of coherent `𝒪_X`-modules on an algebraic space. -/
abbrev Coh {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (SheafOfModules.isCoherent (structureSheaf X)).FullSubcategory

namespace Coh

/-- The inclusion of coherent modules into all module sheaves on `X`. -/
abbrev inclusion {S : Scheme.{u}} (X : AlgebraicSpace S) : Coh X ⥤ Modules X :=
  (SheafOfModules.isCoherent (structureSheaf X)).ι

end Coh

end AlgebraicGeometry.AlgebraicSpace
