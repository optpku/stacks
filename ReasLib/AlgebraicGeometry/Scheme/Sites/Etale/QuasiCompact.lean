/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocallyFiniteType
public import ReasLib.CategoryTheory.Sites.EnoughObjects

/-!
# Quasi-compact basis of the locally finite type étale slice

The quasi-compact object property and the selected étale coverings used as a basis.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Quasi-compact objects of the locally finite type étale slice of `S`. -/
def quasiCompact (S : Scheme.{u}) : ObjectProperty (locallyOfFiniteTypeOver S) :=
  fun V ↦ CompactSpace V.left

/-- An object belongs to the quasi-compact property exactly when its scheme is compact. -/
theorem mem_quasiCompact_iff {S : Scheme.{u}} {V : locallyOfFiniteTypeOver S} :
    quasiCompact S V ↔ CompactSpace V.left :=
  sorry

/-- Étale coverings of `V` whose members are quasi-compact. -/
def coveringSystem (S : Scheme.{u}) (V : locallyOfFiniteTypeOver S) :
    Set (FormalCoproduct.{u} (Over V)) :=
  {cover | ((etaleTopology S).over V).CoversTop cover.obj ∧
    ∀ i : cover.I,
      Etale (cover.obj i).hom.left ∧ CompactSpace (cover.obj i).left.left}

/-- Membership in the selected covering system is the covering and quasi-compactness condition. -/
theorem mem_coveringSystem_iff {S : Scheme.{u}} {V : locallyOfFiniteTypeOver S}
    {cover : FormalCoproduct.{u} (Over V)} :
    cover ∈ coveringSystem S V ↔
      ((etaleTopology S).over V).CoversTop cover.obj ∧
        ∀ i : cover.I,
          Etale (cover.obj i).hom.left ∧ CompactSpace (cover.obj i).left.left :=
  sorry

/-- A selected covering-system family covers its target in the slice étale topology. -/
theorem coveringSystem_isCover {S : Scheme.{u}} {V : locallyOfFiniteTypeOver S}
    {cover : FormalCoproduct.{u} (Over V)} (hcover : cover ∈ coveringSystem S V) :
    ((etaleTopology S).over V).CoversTop cover.obj :=
  sorry

/-- Selected quasi-compact étale coverings refine every étale covering of the target. -/
theorem coveringSystem_cofinal {S : Scheme.{u}} {V : locallyOfFiniteTypeOver S}
    {ι : Type u} (family : ι → Over V)
    (hfamily : ((etaleTopology S).over V).CoversTop family) :
    ∃ cover : FormalCoproduct.{u} (Over V),
      cover ∈ coveringSystem S V ∧
        Nonempty (cover ⟶ FormalCoproduct.mk ι family) :=
  sorry

/-- Every locally finite type object over `S` has an étale covering by quasi-compact objects. -/
theorem hasEnoughQuasiCompactObjects (S : Scheme.{u}) :
    (etaleTopology S).HasEnoughObjectsWithProperty (quasiCompact S) :=
  sorry

/-- The inclusion of quasi-compact objects is cover-dense in the locally finite type étale site. -/
instance hasEnoughQuasiCompact (S : Scheme.{u}) :
    (quasiCompact S).ι.IsCoverDense (etaleTopology S) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
