/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.BaseChange.Restriction
public import Mathlib.CategoryTheory.Adjunction.Mates

@[expose] public section
open CategoryTheory TopologicalSpace Topology Opposite
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
noncomputable section
universe u

namespace AlgebraicGeometry.RingedSpace.OpenSubspace.BaseChange

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier)

/-- The restricted morphism factors the actual open inclusions. -/
theorem square_fac :
    restrictedMorphismToOpen f V ≫ Y.ofRestrict V.isOpenEmbedding =
      X.ofRestrict (preimageOpen f V).isOpenEmbedding ≫ f := by
  apply InducedCategory.hom_ext
  exact PresheafedSpace.IsOpenImmersion.lift_fac
    (Y.ofRestrict V.isOpenEmbedding).hom
    ((X.ofRestrict (preimageOpen f V).isOpenEmbedding).hom ≫ f.hom)
    (fun _ ⟨x, hx⟩ ↦ ⟨⟨f.hom.base x.1, x.2⟩, hx⟩)

/-- The induced map has the actual restricted point map of f. -/
theorem restricted_base (x : (preimageOpen f V)) :
    ((restrictedMorphismToOpen f V).hom.base x).1 = f.hom.base x.1 :=
  congrArg (fun k => k.hom.base x) (square_fac f V)

/-- The two literal base-change models use exactly the same ambient open. -/
theorem sectionOpen_eq (W : Opens (Y.restrict V.isOpenEmbedding).carrier) :
    (Opens.map f.hom.base).obj (V.isOpenEmbedding.functor.obj W) =
      (preimageOpen f V).isOpenEmbedding.functor.obj
        ((Opens.map (restrictedMorphismToOpen f V).hom.base).obj W) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hx : x ∈ preimageOpen f V := by
      change f.hom.base x ∈ V
      rw [← hxy]
      exact y.2
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    have hpoint : (restrictedMorphismToOpen f V).hom.base ⟨x, hx⟩ = y := by
      apply Subtype.ext
      exact (restricted_base f V ⟨x, hx⟩).trans hxy.symm
    change (restrictedMorphismToOpen f V).hom.base ⟨x, hx⟩ ∈ W
    rw [hpoint]
    exact hy
  · rintro ⟨x', hx', rfl⟩
    exact ⟨(restrictedMorphismToOpen f V).hom.base x', hx', restricted_base f V x'⟩

/-- The source literal functor has the action induced by f on image opens. -/
abbrev literalSource := RingedSpace.Hom.pushforward f ⋙ literalRestriction Y V

/-- The target literal functor has the action induced by the restricted map. -/
abbrev literalTarget := literalRestriction X (preimageOpen f V) ⋙
  RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V)

/-- Forward additive section map: restriction along equality of the two actual opens. -/
def sectionHom (M : X.Modules) (W : Opens (Y.restrict V.isOpenEmbedding).carrier) :
    ((literalSource f V).obj M).val.obj (op W) →+
      ((literalTarget f V).obj M).val.obj (op W) :=
  { toFun := M.val.map (eqToHom (sectionOpen_eq f V W).symm).op
    map_zero' := map_zero _
    map_add' := map_add _ }

/-- Inverse additive section map: the reverse restriction, not a chosen inverse. -/
def sectionInv (M : X.Modules) (W : Opens (Y.restrict V.isOpenEmbedding).carrier) :
    ((literalTarget f V).obj M).val.obj (op W) →+
      ((literalSource f V).obj M).val.obj (op W) :=
  { toFun := M.val.map (eqToHom (sectionOpen_eq f V W)).op
    map_zero' := map_zero _
    map_add' := map_add _ }

end AlgebraicGeometry.RingedSpace.OpenSubspace.BaseChange
