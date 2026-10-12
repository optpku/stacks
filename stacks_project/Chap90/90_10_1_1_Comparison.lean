/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Composition
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Transport
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass

/-!
# Comparison of fibre categories along a commuting square

A cleavage of `p.op` turns a commuting square in the base into a 2-commutative square of fibre
categories. The induced functor into the 2-fibre product is `fiberComparison`.
-/

@[expose] public section

open CategoryTheory Limits CategoricalPullback Opposite
open scoped CategoricalPullback

universe u v uF vF

variable {C : Type u} [Category.{v} C]
variable {F : Type uF} [Category.{vF} F]

namespace CategoryTheory.Functor

/-- Successive pushforwards along `f` then `g` are naturally isomorphic to the pushforward along
`f ≫ g`. -/
noncomputable def pushforwardFiberCompIso (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    pushforwardFiberFunctor p χ f ⋙ pushforwardFiberFunctor p χ g ≅
      pushforwardFiberFunctor p χ (f ≫ g) :=
  NatIso.ofComponents
    (fun x ↦
      let xOp := toOpFiber p x
      let yOp := (χ.reindex f.op).obj xOp
      let hRound : toOpFiber p (fromOpFiber p yOp) = yOp := Subtype.ext rfl
      eqToIso (congrArg (fun z ↦ fromOpFiber p ((χ.reindex g.op).obj z)) hRound) ≪≫
        { hom := fromOpFiberHom p ((Cleavage.Reindex.compIso χ f.op g.op).hom.app xOp)
          inv := fromOpFiberHom p ((Cleavage.Reindex.compIso χ f.op g.op).inv.app xOp)
          hom_inv_id := sorry
          inv_hom_id := sorry })
    sorry

/-- Equal base arrows induce naturally isomorphic pushforward fibre functors. -/
noncomputable def pushforwardFiberCongrIso (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} {f g : U ⟶ V} (h : f = g) :
    pushforwardFiberFunctor p χ f ≅ pushforwardFiberFunctor p χ g :=
  NatIso.ofComponents
    (fun x ↦
      { hom :=
          fromOpFiberHom p
            ((Cleavage.Reindex.congrIso χ (congrArg Opposite.op h)).inv.app (toOpFiber p x))
        inv :=
          fromOpFiberHom p
            ((Cleavage.Reindex.congrIso χ (congrArg Opposite.op h)).hom.app (toOpFiber p x))
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The 2-commutative square of fibre categories associated to a commuting square in the base. -/
noncomputable def fiberPushforwardSquare (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) :
    CatCommSqOver (pushforwardFiberFunctor p χ f1) (pushforwardFiberFunctor p χ f2)
      (p.Fiber P) where
  fst := pushforwardFiberFunctor p χ π1
  snd := pushforwardFiberFunctor p χ π2
  iso :=
    pushforwardFiberCompIso p χ π1 f1 ≪≫
      pushforwardFiberCongrIso p χ hw ≪≫
      (pushforwardFiberCompIso p χ π2 f2).symm

/-- The first leg of `fiberPushforwardSquare` is pushforward along `π1`. -/
@[simp]
theorem fiberPushforwardSquare_fst (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) :
    (fiberPushforwardSquare p χ hw).fst = pushforwardFiberFunctor p χ π1 := sorry

/-- The second leg of `fiberPushforwardSquare` is pushforward along `π2`. -/
@[simp]
theorem fiberPushforwardSquare_snd (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) :
    (fiberPushforwardSquare p χ hw).snd = pushforwardFiberFunctor p χ π2 := sorry

/-- The comparison functor from `p.Fiber P` into the 2-fibre product of the pushforwards along `f1` and `f2`. -/
noncomputable def fiberComparison (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) :
    p.Fiber P ⥤
      (pushforwardFiberFunctor p χ f1) ⊡ (pushforwardFiberFunctor p χ f2) :=
  (fiberPushforwardSquare p χ hw).comparison

/-- The first projection of `fiberComparison` on objects is pushforward along `π1`. -/
@[simp]
theorem fiberComparison_obj_fst (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) (y : p.Fiber P) :
    ((fiberComparison p χ hw).obj y).fst = (pushforwardFiberFunctor p χ π1).obj y := sorry

/-- The second projection of `fiberComparison` on objects is pushforward along `π2`. -/
@[simp]
theorem fiberComparison_obj_snd (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) (y : p.Fiber P) :
    ((fiberComparison p χ hw).obj y).snd = (pushforwardFiberFunctor p χ π2).obj y := sorry

/-- The structural isomorphism of `fiberComparison` on objects is the square's 2-cell. -/
@[simp]
theorem fiberComparison_obj_iso (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) (y : p.Fiber P) :
    ((fiberComparison p χ hw).obj y).iso =
      (fiberPushforwardSquare p χ hw).iso.app y := sorry

/-- Objects of `fiberComparison` record the two pushforwards and the structural 2-cell. -/
theorem fiberComparison_spec (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) (y : p.Fiber P) :
    ((fiberComparison p χ hw).obj y).fst = (pushforwardFiberFunctor p χ π1).obj y ∧
      ((fiberComparison p χ hw).obj y).snd = (pushforwardFiberFunctor p χ π2).obj y ∧
      ((fiberComparison p χ hw).obj y).iso =
        (fiberPushforwardSquare p χ hw).iso.app y := sorry

end CategoryTheory.Functor
