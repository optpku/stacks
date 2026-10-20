/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalTransformation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict factorization over a based target

This module contains the target-forgetting and target-overcategory bridges for strict
factorizations of categories over a fixed base.  These constructions concern arbitrary based
categories; groupoid-fibration comparison theorems build on them in a separate module.
-/

@[expose] public section

universe u v uX uX' uX'' uY vX vX' vX'' vY

namespace CategoryTheory

namespace BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {X' : BasedCategory.{vX', uX'} C}
variable {X'' : BasedCategory.{vX'', uX''} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {F : X ⥤ᵇ Y} {f : X' ⥤ᵇ Y} {g : X'' ⥤ᵇ Y}

/-- The underlying functor of a morphism in `Cat/Y` commutes with the projections to `C`. -/
theorem forgetTarget.w
    (h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ
      BasedCategory.ofFunctor f.toFunctor) :
    h.toFunctor ⋙ X'.p = X''.p := sorry
/- Proof strategy: rewrite `X'.p` and `X''.p` using `f.w` and `g.w`; after reassociation,
`h.w` gives the middle equality. -/

/-- Forget a morphism in `Cat/Y` to its underlying morphism in `Cat/C`. The non-Prop functor
component is unchanged; only its compatibility proof is transported along `f.w` and `g.w`. -/
def forgetTarget
    (h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ
      BasedCategory.ofFunctor f.toFunctor) :
    X'' ⥤ᵇ X' :=
  { toFunctor := h.toFunctor
    w := forgetTarget.w h }

/-- The total functor of a target-forgotten factorization morphism is unchanged. -/
@[simp]
theorem forgetTarget.toFunctor
    (h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ
      BasedCategory.ofFunctor f.toFunctor) :
    (forgetTarget h).toFunctor = h.toFunctor := sorry

namespace Factorization

/-- A strict factorization equality induces equality of the underlying functors to `Y.obj`. -/
theorem overTarget.w
    (a : X ⥤ᵇ X') (ha : BasedFunctor.comp a f = F) :
    a.toFunctor ⋙ f.toFunctor = F.toFunctor := sorry
/- Proof strategy: apply `congrArg BasedFunctor.toFunctor` to `ha`. -/

/-- Regard a strict factorization `a ⋙ f = F` as the corresponding morphism in `Cat/Y`.
The functor component is exactly `a.toFunctor`; the factorization equality supplies only the
compatibility field. -/
def overTarget
    (a : X ⥤ᵇ X') (ha : BasedFunctor.comp a f = F) :
    BasedCategory.ofFunctor F.toFunctor ⥤ᵇ
      BasedCategory.ofFunctor f.toFunctor :=
  { toFunctor := a.toFunctor
    w := overTarget.w a ha }

/-- The total functor of the morphism over a factorization target is the total functor of the
factorizing based functor. -/
@[simp]
theorem overTarget.toFunctor
    (a : X ⥤ᵇ X') (ha : BasedFunctor.comp a f = F) :
    (overTarget a ha).toFunctor = a.toFunctor := sorry

end Factorization

end BasedFunctor

namespace BasedNatTrans

variable {C : Type u} [Category.{v} C]
variable {X' : BasedCategory.{vX', uX'} C}
variable {X'' : BasedCategory.{vX'', uX''} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {f : X' ⥤ᵇ Y} {g : X'' ⥤ᵇ Y}
variable {h k l : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ
  BasedCategory.ofFunctor f.toFunctor}

/-- The total natural transformation of a `2`-morphism in `Cat/Y` is over the
identity after forgetting the target from `Y` to `C`. -/
theorem forgetTarget.overId (eta : h ⟶ k) :
    eqToHom (BasedFunctor.forgetTarget h).w.symm ≫
        Functor.whiskerRight eta.toNatTrans X'.p ≫
          eqToHom (BasedFunctor.forgetTarget k).w =
      𝟙 X''.p := sorry

/-- Forget a `2`-morphism in `Cat/Y` to its underlying `2`-morphism in
`Cat/C`.  The total natural transformation is unchanged. -/
def forgetTarget (eta : h ⟶ k) :
    BasedFunctor.forgetTarget h ⟶ BasedFunctor.forgetTarget k :=
  BasedNatTrans.ofOverId eta.toNatTrans (forgetTarget.overId eta)

/-- The total natural transformation of a target-forgotten `2`-morphism is unchanged. -/
@[simp]
theorem forgetTarget.toNatTrans (eta : h ⟶ k) :
    (forgetTarget eta).toNatTrans = eta.toNatTrans := sorry

/-- Target forgetting leaves every total-category component of a `2`-morphism unchanged. -/
@[simp]
theorem forgetTarget.app (eta : h ⟶ k) (x : X''.obj) :
    (forgetTarget eta).toNatTrans.app x = eta.toNatTrans.app x := sorry

/-- Forgetting the identity `2`-morphism in `Cat/Y` gives the identity
`2`-morphism in `Cat/C`. -/
@[simp]
theorem forgetTarget.id (h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ
    BasedCategory.ofFunctor f.toFunctor) :
    forgetTarget (𝟙 h) = 𝟙 (BasedFunctor.forgetTarget h) := sorry

/-- Forgetting a vertical composite in `Cat/Y` gives the corresponding
vertical composite in `Cat/C`. -/
@[simp]
theorem forgetTarget.comp (eta : h ⟶ k) (theta : k ⟶ l) :
    forgetTarget (eta ≫ theta) = forgetTarget eta ≫ forgetTarget theta := sorry

end BasedNatTrans

namespace BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X' : BasedCategory.{vX', uX'} C}
variable {X'' : BasedCategory.{vX'', uX''} C}
variable {Y : BasedCategory.{vY, uY} C}

/-- Forgetting the target of a strict factorization is functorial on the
corresponding hom-category. -/
def forgetTarget.functor (f : X' ⥤ᵇ Y) (g : X'' ⥤ᵇ Y) :
    (BasedCategory.ofFunctor g.toFunctor ⥤ᵇ
      BasedCategory.ofFunctor f.toFunctor) ⥤ (X'' ⥤ᵇ X') where
  obj := forgetTarget
  map := BasedNatTrans.forgetTarget
  map_id := BasedNatTrans.forgetTarget.id
  map_comp := BasedNatTrans.forgetTarget.comp

/-- The object action of target forgetting is `BasedFunctor.forgetTarget`. -/
@[simp]
theorem forgetTarget.functor.obj
    (f : X' ⥤ᵇ Y) (g : X'' ⥤ᵇ Y)
    (h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ
      BasedCategory.ofFunctor f.toFunctor) :
    (forgetTarget.functor f g).obj h = forgetTarget h := sorry

/-- The morphism action of target forgetting is `BasedNatTrans.forgetTarget`. -/
@[simp]
theorem forgetTarget.functor.map
    (f : X' ⥤ᵇ Y) (g : X'' ⥤ᵇ Y)
    {h k : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ
      BasedCategory.ofFunctor f.toFunctor} (eta : h ⟶ k) :
    (forgetTarget.functor f g).map eta = BasedNatTrans.forgetTarget eta := sorry

/- Axiom audit: the non-Prop payloads of `forgetTarget` and `Factorization.overTarget` are exactly the
supplied total functors. Their `sorryAx` dependency is confined to the Prop-valued commuting
fields. -/

end BasedFunctor

end CategoryTheory
