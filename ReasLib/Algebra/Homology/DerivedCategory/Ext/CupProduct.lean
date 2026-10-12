/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.Abelian.Ext

/-- The source-order Yoneda cup product in the Ext groups of an abelian category. -/
noncomputable def cupProduct {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {F G H : C} {i j : ℕ}
    (α : Ext G H i) (β : Ext F G j) :
    Ext F H (i + j) :=
  β.comp α (Nat.add_comm j i)

/-- The additive bilinear map underlying the source-order Yoneda cup product. -/
noncomputable def cupProductHom {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    (F G H : C) (i j : ℕ) :
    Ext G H i →+ Ext F G j →+ Ext F H (i + j) :=
  (bilinearComp F G H j i (i + j) (Nat.add_comm j i)).flip

end CategoryTheory.Abelian.Ext
