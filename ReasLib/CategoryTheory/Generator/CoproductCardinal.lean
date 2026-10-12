/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import ReasLib.CategoryTheory.Subobject.Cardinal

@[expose] public section

/-!
# Subobject Cardinals of Constant Coproducts

This module records the cardinal monotonicity used when a family of copies of a generator is
enlarged along an embedding of index types. The statements apply to any object; being a
generator is relevant only to their principal applications.
-/

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCoproducts.{w} C]

/-- The subobject cardinal of a constant coproduct with `kappa` summands. The cardinal lives in
the coproduct universe, so its chosen representative can be used directly as the index type. -/
@[stacks 079J "cardinal growth function"]
noncomputable abbrev coproductCardinal (G : C) (kappa : Cardinal.{w}) : Cardinal :=
  Cardinal.mk (Subobject (∐ fun _ : kappa.out ↦ G))

/-- Computing `coproductCardinal` with any index type of cardinality `kappa` gives the same
answer. Thus downstream statements do not depend on the representative selected by `kappa.out`. -/
theorem cardinalMk_coprod_const_eq_coproductCardinal
    (G : C) (kappa : Cardinal.{w}) {I : Type w} (hI : Cardinal.mk I = kappa) :
    Cardinal.mk (Subobject (∐ fun _ : I ↦ G)) = coproductCardinal G kappa := sorry

/-- Equivalent index types give equal subobject cardinals for the corresponding constant
coproducts. -/
theorem cardinalMk_coprod_const_eq_of_equiv (G : C) {I J : Type w} (e : I ≃ J) :
    Cardinal.mk (Subobject (∐ fun _ : I ↦ G)) =
      Cardinal.mk (Subobject (∐ fun _ : J ↦ G)) := sorry

/-- An embedding of index types induces a subobject-cardinality inequality between the
corresponding constant coproducts. -/
theorem cardinalMk_coprod_const_le_of_embedding (G : C) {I J : Type w} (e : I ↪ J) :
    Cardinal.mk (Subobject (∐ fun _ : I ↦ G)) ≤
      Cardinal.mk (Subobject (∐ fun _ : J ↦ G)) := sorry

/-- A cardinal bound on `Subobject X` gives the corresponding bound between constant
coproducts indexed by canonical small representatives. -/
theorem cardinalMk_coprod_const_le_of_cardinalMk_le
    (G : C) {X : C} {kappa : Cardinal.{max u v}}
    [Small.{w} (Subobject X)] [Small.{w} kappa.out]
    (hX : Cardinal.mk (Subobject X) ≤ kappa) :
    Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} (Subobject X) ↦ G)) ≤
      Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} kappa.out ↦ G)) := sorry

/-- Enlarging the number of summands can only enlarge `coproductCardinal`. -/
theorem coproductCardinal_mono (G : C) {kappa lambda : Cardinal.{w}}
    (h : kappa ≤ lambda) :
    coproductCardinal G kappa ≤ coproductCardinal G lambda := sorry

end CategoryTheory.Subobject
