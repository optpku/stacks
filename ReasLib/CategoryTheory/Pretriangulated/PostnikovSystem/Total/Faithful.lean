/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Evaluation
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Joint faithfulness for total Postnikov systems

The projection to finite rows does not by itself detect morphisms in the total
category: a morphism also carries one map on every auxiliary `Y` object.  This
file packages both pieces of data in one canonical functor.  The target uses a
product with the category of functors from a finite discrete index, so the API
remains independent of a chosen product object in `D`.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]
variable {n : ℕ}

variable (D) in
/-- The discrete family of auxiliary objects carried by a total Postnikov system.

The morphism component at `i` is the stored `yMap i`; no choices of finite
products or coproducts in `D` are involved.
-/
@[stacks 0D7Z "family of auxiliary-object evaluations"]
def auxFamily (n : ℕ) :
    Total D n ⥤ (Discrete (Fin (n + 1)) ⥤ D) where
  obj P := Discrete.functor (fun i => P.system i)
  map {P Q} f :=
    { app := fun i => f.systemMap.yMap i.as
      naturality := sorry }
  map_id P := sorry
  map_comp f g := sorry

/-- The auxiliary-family evaluation computes to the stored `Y` object. -/
@[simp, stacks 0D7Z "auxiliary-family object computation"]
theorem auxFamily_obj (P : Total D n) (i : Fin (n + 1)) :
    ((auxFamily D n).obj P).obj (Discrete.mk i) = P.system i := sorry

/-- The auxiliary-family evaluation computes to the stored `yMap` component. -/
@[simp, stacks 0D7Z "auxiliary-family morphism computation"]
theorem auxFamily_map_app {P Q : Total D n} (f : P ⟶ Q) (i : Fin (n + 1)) :
    ((auxFamily D n).map f).app (Discrete.mk i) = f.systemMap.yMap i := sorry

variable (D) in
/-- Joint evaluation of the underlying finite row and all auxiliary `Y` objects. -/
@[stacks 0D7Z "joint row and auxiliary evaluation"]
def joint (n : ℕ) :
    Total D n ⥤ ComposableArrows D n × (Discrete (Fin (n + 1)) ⥤ D) :=
  (forget D n).prod' (auxFamily D n)

/-- The first component of a jointly evaluated object is its underlying finite row. -/
@[simp, stacks 0D7Z "joint evaluation row computation"]
theorem joint_obj_fst (P : Total D n) :
    ((joint D n).obj P).1 = P.base := sorry

/-- The second component of a jointly evaluated object is its discrete auxiliary family. -/
@[simp, stacks 0D7Z "joint evaluation auxiliary-family computation"]
theorem joint_obj_snd (P : Total D n) :
    ((joint D n).obj P).2 = Discrete.functor (fun i => P.system i) := sorry

/-- The first component of a jointly evaluated morphism is its base map. -/
@[simp, stacks 0D7Z "joint evaluation base-map computation"]
theorem joint_map_fst {P Q : Total D n} (f : P ⟶ Q) :
    ((joint D n).map f).1 = f.base := sorry

/-- The `i`th component of the auxiliary part of a jointly evaluated morphism is `yMap i`. -/
@[simp, stacks 0D7Z "joint evaluation auxiliary-map computation"]
theorem joint_map_snd_app {P Q : Total D n} (f : P ⟶ Q) (i : Fin (n + 1)) :
    (((joint D n).map f).2).app (Discrete.mk i) = f.systemMap.yMap i := sorry

/-- Joint evaluation is faithful: the base map and every auxiliary-object map determine a total
morphism. -/
@[stacks 0D7Z "faithfulness of joint row and auxiliary evaluation"]
instance joint_faithful (n : ℕ) : (joint D n).Faithful := sorry

/-- A direct `Hom.ext` bridge through the jointly evaluated morphism. -/
@[ext (iff := false), stacks 0D7Z "joint evaluation hom extensionality"]
theorem hom_ext_of_joint {P Q : Total D n} {f g : P ⟶ Q}
    (h : (joint D n).map f = (joint D n).map g) : f = g := sorry

/-- The joint evaluation equality criterion in component form. -/
@[simp, stacks 0D7Z "joint evaluation equality criterion"]
theorem joint_map_eq_iff {P Q : Total D n} {f g : P ⟶ Q} :
    (joint D n).map f = (joint D n).map g ↔
      f.base = g.base ∧ ∀ i, f.systemMap.yMap i = g.systemMap.yMap i := sorry

end CategoryTheory.PostnikovSystem.Total

end
