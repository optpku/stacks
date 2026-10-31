/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The range of a monomorphic simplicial map

A monomorphic simplicial map identifies its source with its range subcomplex. This file exposes
an explicit inverse whose degreewise data is independent of the proof that the map is monic.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace SSet.Subcomplex.toRange

/-- The unique chosen preimage of an element in the range of a monomorphic simplicial map. -/
@[stacks 018P "preimage map on a monomorphic simplicial-map range"]
noncomputable def inv.app {X Y : SSet.{u}} (f : X ⟶ Y)
    [Mono f] (Δ : SimplexCategoryᵒᵖ) :
    (Subcomplex.range f).toSSet.obj Δ ⟶ X.obj Δ :=
  TypeCat.ofHom (fun x : ↥((Subcomplex.range f).obj Δ) ↦
    Classical.choose (Subtype.property x))

/-- The chosen preimage followed by the range map is the identity on each range degree. -/
@[reassoc (attr := simp), stacks 018P "degreewise range-source inverse law"]
theorem app_inv_hom_id {X Y : SSet.{u}} (f : X ⟶ Y)
    [Mono f] (Δ : SimplexCategoryᵒᵖ) :
    inv.app f Δ ≫ (Subcomplex.toRange f).app Δ =
      𝟙 ((Subcomplex.range f).toSSet.obj Δ) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  exact Classical.choose_spec (Subtype.property x)

/-- The range map followed by the chosen preimage is the identity on each source degree. -/
@[reassoc (attr := simp), stacks 018P "degreewise source-range inverse law"]
theorem app_hom_inv_id {X Y : SSet.{u}} (f : X ⟶ Y)
    [Mono f] (Δ : SimplexCategoryᵒᵖ) :
    (Subcomplex.toRange f).app Δ ≫ inv.app f Δ = 𝟙 (X.obj Δ) := by
  apply (cancel_mono ((Subcomplex.toRange f).app Δ)).1
  rw [Category.assoc, app_inv_hom_id, Category.comp_id, Category.id_comp]

/-- For a monomorphic simplicial map, the chosen preimage maps are natural in the degree. -/
@[stacks 018P "naturality of the preimage map on a monomorphic range"]
theorem inv.app_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    [Mono f] {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (g : Δ₁ ⟶ Δ₂) :
    (Subcomplex.range f : SSet).map g ≫ inv.app f Δ₂ =
      inv.app f Δ₁ ≫ X.map g := by
  apply (cancel_mono ((Subcomplex.toRange f).app Δ₂)).1
  rw [Category.assoc, app_inv_hom_id, Category.comp_id]
  rw [Category.assoc, (Subcomplex.toRange f).naturality g, ← Category.assoc,
    app_inv_hom_id, Category.id_comp]

/-- The explicit inverse from the range of a monomorphic simplicial map to its source. -/
@[stacks 018P "explicit inverse map of a monomorphic simplicial-map range"]
noncomputable def inv {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    (Subcomplex.range f : SSet) ⟶ X where
  app Δ := inv.app f Δ
  naturality := fun _ _ g ↦ inv.app_naturality f g

/-- The canonical map to the range of a monomorphic simplicial map followed by its explicit
inverse is the identity. -/
@[stacks 018P "source-range inverse law"]
theorem hom_inv_id {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Subcomplex.toRange f ≫ inv f = 𝟙 X := by
  apply NatTrans.ext
  funext Δ
  exact app_hom_inv_id f Δ

/-- The explicit inverse of the range map of a monomorphic simplicial map followed by the
canonical map is the identity. -/
@[stacks 018P "range-source inverse law"]
theorem inv_hom_id {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    inv f ≫ Subcomplex.toRange f = 𝟙 (Subcomplex.range f : SSet) := by
  apply NatTrans.ext
  funext Δ
  exact app_inv_hom_id f Δ

/-- A monomorphic simplicial map identifies its source with its range. -/
@[stacks 018P "source-range isomorphism of a monomorphic simplicial map"]
noncomputable def iso {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    X ≅ (Subcomplex.range f : SSet) :=
  { hom := Subcomplex.toRange f
    inv := inv f
    hom_inv_id := Subcomplex.toRange.hom_inv_id f
    inv_hom_id := Subcomplex.toRange.inv_hom_id f }

/-- The forward map of `Subcomplex.toRange.iso` is the canonical map to the range. -/
@[simp, stacks 018P "forward source-range comparison"]
theorem iso_hom {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    (iso f).hom = Subcomplex.toRange f := rfl

/-- The inverse map of `Subcomplex.toRange.iso` is the named preimage map. -/
@[simp, stacks 018P "inverse source-range comparison"]
theorem iso_inv {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    (iso f).inv = inv f := rfl

/-- The canonical source-range comparison followed by the range inclusion is the original map. -/
@[reassoc, stacks 018P "source-range comparison over the codomain"]
theorem iso.hom_comp_ι {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    (iso f).hom ≫ (Subcomplex.range f).ι = f :=
  Subcomplex.toRange_ι f

/-- The inverse source-range comparison followed by the original map is the range inclusion. -/
@[reassoc, stacks 018P "inverse source-range comparison over the codomain"]
theorem iso.inv_comp {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    (iso f).inv ≫ f = (Subcomplex.range f).ι := by
  calc
    (iso f).inv ≫ f =
        (iso f).inv ≫ ((iso f).hom ≫ (Subcomplex.range f).ι) := by
      rw [iso.hom_comp_ι]
    _ = _ := by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SSet.Subcomplex.toRange
