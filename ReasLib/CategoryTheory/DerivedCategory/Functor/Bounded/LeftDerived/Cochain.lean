/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Canonical
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps out of bounded-above left-derived values

This file turns a morphism of bounded-above cochain complexes `F(K) ⟶ G` into the canonical
morphism `LF(K) ⟶ G` in the bounded-above derived category.  It owns the comparison between
termwise mapping before the homotopy quotient and the induced bounded homotopy functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.Bounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]
  [F.toBoundedAboveDerived.HasLeftDerivedFunctor
    (HomotopyCategory.Minus.quasiIso A)]

/-- A morphism `F(K) ⟶ G` of bounded-above cochain complexes induces the canonical morphism
from the bounded-above left-derived value of `F` at `K` to `G`. -/
@[stacks 01F8 "bounded left-derived map from a cochain map"]
noncomputable def fromCochainMap
    {K : CochainComplex.Minus A} {G : CochainComplex.Minus B}
    (φ : (Functor.Cochain.Minus.map F).obj K ⟶ G) :
    (functor F).obj
        ((DerivedCategory.Minus.Qh A).obj
          ((HomotopyCategory.Minus.quotient A).obj K)) ⟶
      (DerivedCategory.Minus.Qh B).obj
        ((HomotopyCategory.Minus.quotient B).obj G) :=
  (counit F).app ((HomotopyCategory.Minus.quotient A).obj K) ≫
    (DerivedCategory.Minus.Qh B).map
      ((Functor.Homotopy.Minus.quotientIso F).inv.app K) ≫
    (DerivedCategory.Minus.Qh B).map
      ((HomotopyCategory.Minus.quotient B).map φ)

/-- The canonical bounded left-derived morphism induced by a cochain map is natural in its
argument and target. -/
@[stacks 01F8 "naturality of the bounded left-derived map from a cochain map"]
theorem fromCochainMap_natural
    {K₁ K₂ : CochainComplex.Minus A} {G₁ G₂ : CochainComplex.Minus B}
    (φ₁ : (Functor.Cochain.Minus.map F).obj K₁ ⟶ G₁)
    (φ₂ : (Functor.Cochain.Minus.map F).obj K₂ ⟶ G₂)
    (β : K₁ ⟶ K₂) (α : G₁ ⟶ G₂)
    (hcomm : (Functor.Cochain.Minus.map F).map β ≫ φ₂ = φ₁ ≫ α) :
    CommSq
      ((functor F).map
        ((DerivedCategory.Minus.Qh A).map
          ((HomotopyCategory.Minus.quotient A).map β)))
      (fromCochainMap F φ₁)
      (fromCochainMap F φ₂)
      ((DerivedCategory.Minus.Qh B).map
        ((HomotopyCategory.Minus.quotient B).map α)) := sorry

end CategoryTheory.Functor.LeftDerived.Bounded
