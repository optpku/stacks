/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps into Bounded-Below Right-Derived Values

This file turns a morphism of bounded-below cochain complexes `G ⟶ F(K)` into the canonical
morphism `G ⟶ RF(K)` in the bounded-below derived category.  It owns the comparison between
termwise mapping before the homotopy quotient and the induced bounded homotopy functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]
  [F.toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso A)]

/-- A morphism `G ⟶ F(K)` of bounded-below cochain complexes induces the canonical morphism
from `G` to the bounded-below right-derived value of `F` at `K`. -/
@[stacks 01F8 "bounded right-derived map from a cochain map"]
noncomputable def fromCochainMap
    {G : CochainComplex.Plus B} {K : CochainComplex.Plus A}
    (φ : G ⟶ F.mapCochainComplexPlus.obj K) :
    DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient B).obj G) ⟶
      (functor F).obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient A).obj K)) :=
  DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient B).map φ) ≫
    DerivedCategory.Plus.Qh.map
      ((Functor.Homotopy.Plus.quotientIso F).hom.app K) ≫
    (unit F).app ((HomotopyCategory.Plus.quotient A).obj K)

/-- The canonical bounded right-derived morphism induced by a cochain map is natural in its
source and argument. -/
@[stacks 01F8 "naturality of the bounded right-derived map from a cochain map"]
theorem fromCochainMap_natural
    {G₁ G₂ : CochainComplex.Plus B} {K₁ K₂ : CochainComplex.Plus A}
    (φ₁ : G₁ ⟶ F.mapCochainComplexPlus.obj K₁)
    (φ₂ : G₂ ⟶ F.mapCochainComplexPlus.obj K₂)
    (α : G₁ ⟶ G₂) (β : K₁ ⟶ K₂)
    (hcomm : φ₁ ≫ F.mapCochainComplexPlus.map β = α ≫ φ₂) :
    CommSq
      (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient B).map α))
      (fromCochainMap F φ₁)
      (fromCochainMap F φ₂)
      ((functor F).map
        (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient A).map β))) := sorry

end CategoryTheory.Functor.RightDerived.Bounded
