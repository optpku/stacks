/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap100.Definition_100_5_1_Surjective

/-!
# Descent of surjectivity for morphisms of algebraic stacks

If a morphism of algebraic stacks becomes surjective after base change along a
surjective morphism, then the original morphism is surjective. The core
statement is for an arbitrary bilimit `PseudoPullbackCone`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Surjective

/-- Surjectivity of a morphism of algebraic stacks descends along the second
projection of any bilimit `PseudoPullbackCone` of a surjective morphism. -/
theorem of_isBilimit_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Surjective g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [Surjective c.snd] : Surjective f :=
  sorry

/-- Surjectivity of a morphism of algebraic stacks descends along the first
projection of a chosen 2-fibre product of a surjective morphism. -/
theorem of_twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [Surjective (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)] :
    Surjective g :=
  sorry

/-- After base change along a surjective morphism of algebraic stacks, the
original morphism is surjective if and only if the second projection of a
bilimit `PseudoPullbackCone` is surjective. -/
theorem isBilimit_snd_iff {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Surjective g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    Surjective c.snd ↔ Surjective f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Surjective
