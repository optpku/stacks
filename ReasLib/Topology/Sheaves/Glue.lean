/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Chosen gluings of compatible sheaf sections

The sheaf condition gives a unique gluing propositionally.  This file provides
one noncomputable representative together with the restriction computation API
needed by constructions that must return an actual section.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace TopologicalSpace.Opens

universe x

namespace TopCat.Presheaf

variable {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable [HasLimitsOfSize.{x, x} C] [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [PreservesLimitsOfSize.{x, x} (CategoryTheory.forget C)]
variable {X : TopCat.{x}}

/-- Sections over a pairwise disjoint family of open subsets are automatically compatible. -/
@[stacks 0A3F "compatible sections on pairwise disjoint opens"]
theorem isCompatible_of_pairwise_disjoint
    (F : TopCat.Sheaf C X) {ι : Type*} (U : ι → Opens X)
    (hU : Pairwise fun i j ↦ Disjoint (U i) (U j))
    (s : ∀ i, ToType (F.obj.obj (op (U i)))) :
    IsCompatible F.obj U s := sorry

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable [HasLimitsOfSize.{x, x} C] [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [PreservesLimitsOfSize.{x, x} (CategoryTheory.forget C)]
variable {X : TopCat.{x}}

/-- A chosen gluing of a compatible family of sections over a cover of `V`.

The choice is encapsulated by `glueOfCompatibleFamily_spec`; downstream code
should use that restriction formula instead of inspecting the chosen section. -/
@[stacks 0A3F "chosen gluing of a compatible family"]
noncomputable def glueOfCompatibleFamily (F : TopCat.Sheaf C X) {ι : Type*}
    (U : ι → Opens X) (V : Opens X) (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (s : ∀ i, ToType (F.obj.obj (Opposite.op (U i))))
    (hs : TopCat.Presheaf.IsCompatible F.obj U s) :
    ToType (F.obj.obj (Opposite.op V)) :=
  let P := F.obj ⋙ CategoryTheory.forget C
  let hP : TopCat.Presheaf.IsSheaf P :=
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (CategoryTheory.forget C) F.obj).mp F.property
  let t := (hP.isSheafPairwiseIntersections U).some
  let compatibleSection := TopCat.Presheaf.IsCompatible.sectionPairwise (F := P) hs
  let glued := t.lift (Types.coneOfSection compatibleSection.property) PUnit.unit
  F.obj.map (eqToHom (le_antisymm hcover (iSup_le fun i ↦ (iUV i).le))).op glued

/-- Restricting a chosen gluing to a member of the cover recovers its prescribed local section. -/
@[stacks 0A3F "restriction of a chosen compatible gluing"]
theorem glueOfCompatibleFamily_spec (F : TopCat.Sheaf C X) {ι : Type*}
    (U : ι → Opens X) (V : Opens X) (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (s : ∀ i, ToType (F.obj.obj (Opposite.op (U i))))
    (hs : TopCat.Presheaf.IsCompatible F.obj U s) (i : ι) :
    F.obj.map (iUV i).op (F.glueOfCompatibleFamily U V iUV hcover s hs) = s i := sorry

/-- A section over `V` agreeing with the prescribed family on the cover is the chosen gluing. -/
@[stacks 0A3F "uniqueness of a chosen compatible gluing"]
theorem eq_glueOfCompatibleFamily (F : TopCat.Sheaf C X) {ι : Type*}
    (U : ι → Opens X) (V : Opens X) (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (s : ∀ i, ToType (F.obj.obj (Opposite.op (U i))))
    (hs : TopCat.Presheaf.IsCompatible F.obj U s)
    (t : ToType (F.obj.obj (Opposite.op V)))
    (ht : ∀ i, F.obj.map (iUV i).op t = s i) :
    t = F.glueOfCompatibleFamily U V iUV hcover s hs := sorry

end TopCat.Sheaf


