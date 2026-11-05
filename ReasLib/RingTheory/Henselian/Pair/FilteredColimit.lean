/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Adjunction.Limits
public import ReasLib.RingTheory.Henselian.Pair.Category
import ReasLib.RingTheory.Henselian.DirectLimit
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered colimits of pair Henselizations

The inclusion of Henselian pairs preserves filtered colimits. Together with preservation
of colimits by the Henselization left adjoint, this gives preservation of filtered
colimits by Henselization as an endofunctor of ordinary ring pairs.

@stack 0A04
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace RingPairCat

/-- The pair morphism induced by a ring map carrying the distinguished ideal into
its target ideal. Its quotient component is the canonical quotient map. -/
private def colimitPairHom {X Y : RingPairCat.{u}} (f : X.ring →+* Y.ring)
    (hf : X.ideal ≤ Ideal.comap f Y.ideal) : X ⟶ Y :=
  InducedCategory.homMk <|
    Arrow.homMk' (CommRingCat.ofHom f)
      (CommRingCat.ofHom (Ideal.quotientMap Y.ideal f hf)) (by ext x; rfl)

/-- On a directed preorder, use the actual ring direct limit and the supremum
of the images of the stage ideals. All cocone and descent maps are induced by
`Ring.DirectLimit.of` and `Ring.DirectLimit.lift`. -/
private theorem henselianPairInclusion_preserves_directed (J : Type u)
    [Preorder J] [Nonempty J] [IsDirectedOrder J] :
    PreservesColimitsOfShape J henselianPairInclusion.{u} := by
  classical
  constructor
  intro F
  let A : J → Type u := fun j ↦ (F.obj j).obj.ring
  let I : ∀ j, Ideal (A j) := fun j ↦ (F.obj j).obj.ideal
  let f : ∀ i j : J, i ≤ j → A i →+* A j :=
    fun i j h ↦ ringHom (F.map (homOfLE h)).hom
  haveI : DirectedSystem A (fun i j h ↦ f i j h) := {
    map_self {i} x := by
      change ringHom (F.map (𝟙 i)).hom x = x
      simp only [F.map_id]
      rfl
    map_map {k j i} hij hjk x := by
      change ringHom (F.map (homOfLE hjk)).hom
          (ringHom (F.map (homOfLE hij)).hom x) =
        ringHom (F.map (homOfLE (hij.trans hjk))).hom x
      change ringHom ((F.map (homOfLE hij) ≫ F.map (homOfLE hjk)).hom) x = _
      rw [← F.map_comp]
      rfl }
  haveI : ∀ j, HenselianRing (A j) (I j) := fun j ↦ (F.obj j).property
  let L := Ring.DirectLimit A (fun i j h ↦ f i j h)
  let ofL (j : J) : A j →+* L := Ring.DirectLimit.of A (fun i j h ↦ f i j h) j
  let IL : Ideal L := ⨆ j, Ideal.map (ofL j) (I j)
  let X : RingPairCat.{u} := mk (CommRingCat.of L) IL
  have hX : henselianPairProperty X :=
    Ring.DirectLimit.directedSystem_directLimit_henselianRing A I f
      (fun {i j} h ↦ Ideal.map_le_iff_le_comap.mpr
        (ringHom_ideal_le_comap (F.map (homOfLE h)).hom))
  let leg (j : J) : (F.obj j).obj ⟶ X :=
    colimitPairHom (ofL j) (Ideal.map_le_iff_le_comap.mp (le_iSup (fun j ↦
      Ideal.map (ofL j) (I j)) j))
  let c : Cocone F :=
    { pt := ⟨X, hX⟩
      ι :=
        { app := fun j ↦ ObjectProperty.homMk (leg j)
          naturality := by
            intro i j h
            apply ObjectProperty.hom_ext
            apply hom_ext
            ext x
            change ofL j (f i j (leOfHom h) x) = ofL i x
            exact Ring.DirectLimit.of_f (G := A) (f := fun i j h ↦ f i j h) (leOfHom h) x } }
  let descRing (s : Cocone (F ⋙ henselianPairInclusion)) : L →+* s.pt.ring :=
    Ring.DirectLimit.lift A (fun i j h ↦ f i j h) s.pt.ring
      (fun j ↦ ringHom (s.ι.app j))
      (fun i j h x ↦ by
        exact congrArg (fun g ↦ ringHom g x) (s.w (homOfLE h)))
  have descIdeal (s : Cocone (F ⋙ henselianPairInclusion)) :
      IL ≤ Ideal.comap (descRing s) s.pt.ideal := by
    apply iSup_le
    intro j
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change descRing s (ofL j x) ∈ s.pt.ideal
    change Ring.DirectLimit.lift A (fun i j h ↦ f i j h) s.pt.ring
      (fun j ↦ ringHom (s.ι.app j)) _ (Ring.DirectLimit.of A _ j x) ∈ s.pt.ideal
    rw [Ring.DirectLimit.lift_of]
    exact ringHom_ideal_le_comap (s.ι.app j) hx
  let hc : IsColimit (henselianPairInclusion.mapCocone c) :=
    { desc := fun s ↦ colimitPairHom (descRing s) (descIdeal s)
      fac := by
        intro s j
        apply hom_ext
        ext x
        change descRing s (ofL j x) = ringHom (s.ι.app j) x
        exact Ring.DirectLimit.lift_of (G := A) (f := fun i j h ↦ f i j h)
          s.pt.ring (fun j ↦ ringHom (s.ι.app j)) _ j x
      uniq := by
        intro s m hm
        apply hom_ext
        apply Ring.DirectLimit.hom_ext
        intro j
        ext x
        have h := congrArg (fun g ↦ ringHom g x) (hm j)
        change ringHom m (ofL j x) = ringHom (s.ι.app j) x at h
        change ringHom m (ofL j x) = descRing s (ofL j x)
        rw [h]
        exact (Ring.DirectLimit.lift_of (G := A) (f := fun i j h ↦ f i j h)
          s.pt.ring (fun j ↦ ringHom (s.ι.app j)) _ j x).symm }
  let hcH : IsColimit c :=
    { desc := fun s ↦ ObjectProperty.homMk (hc.desc (henselianPairInclusion.mapCocone s))
      fac := by
        intro s j
        apply ObjectProperty.hom_ext
        exact hc.fac (henselianPairInclusion.mapCocone s) j
      uniq := by
        intro s m hm
        apply ObjectProperty.hom_ext
        exact hc.uniq (henselianPairInclusion.mapCocone s) m.hom
          (fun j ↦ congrArg (fun g ↦ g.hom) (hm j)) }
  exact preservesColimit_of_preserves_colimit_cocone hcH hc

/-- Filtered colimits of Henselian pairs are computed in ordinary ring pairs.
The directed case uses the existing Henselian-ring direct-limit theorem, and
an arbitrary small filtered category admits a final directed preorder. -/
@[stacks 0FWT "filtered colimits of Henselian pairs", instance]
theorem henselianPairInclusion_preservesFilteredColimits :
    PreservesFilteredColimits henselianPairInclusion.{u} := by
  constructor
  intro J _ _
  obtain ⟨K, _, _, _, G, _⟩ := IsFiltered.exists_directed J
  haveI : PreservesColimitsOfShape K henselianPairInclusion.{u} :=
    henselianPairInclusion_preserves_directed K
  exact Functor.Final.preservesColimitsOfShape_of_final G henselianPairInclusion

/-- Lemma 15.12.5: pair Henselization preserves filtered colimits in ordinary ring pairs.
The right-adjoint witness is an explicit parameter so the statement does not select
Henselization data from the deferred existence theorem. -/
@[stacks 0A04 "Lemma 15.12.5"]
instance pairHenselization_preservesFilteredColimits
    [henselianPairInclusion.{u}.IsRightAdjoint] :
    PreservesFilteredColimits
      (henselianPairInclusion.leftAdjoint ⋙ henselianPairInclusion) := by
  infer_instance

end RingPairCat
