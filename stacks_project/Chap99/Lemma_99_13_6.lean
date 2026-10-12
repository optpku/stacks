/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap99.Lemma_99_13_6_Hom

/-!
# Lemma 99.13.6

The projection `pFpFlatProperGroupoids S : FpFlatProperGroupoids S ⥤ Over S`
is limit preserving in the sense of Artin's Axioms, Definition 98.11.1. The
Hom-universe of `FpFlatProperGroupoids S` is `u + 1`, so this cannot be stated
as `AlgebraicGeometry.Groupoids.LimitPreserving` on `GroupoidsOver S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open CategoryTheory.Functor.Fiber
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace FpFlatProperGroupoids

/-- Lemma 99.13.6: the stack
`pFpFlatProperGroupoids S : FpFlatProperGroupoids S ⥤ Over S` is limit
preserving in the sense of Artin's Axioms, Definition 98.11.1: directed inverse
limits of affine schemes over `S` induce equivalences of fibre categories. -/
@[stacks 0D1I]
theorem isLimitPreserving (S : Scheme.{u})
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left) :
    (∀ x : (pFpFlatProperGroupoids S).Fiber c.pt,
      ∃ (i : I) (xi : (pFpFlatProperGroupoids S).Fiber (D.obj i)),
        IsIsomorphic (restrictObj xi (c.π.app i)) x) ∧
      ∀ (i : I) (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i)),
        Nonempty (IsColimit (homCocone S c x y)) :=
  sorry

/-- Object descent for `pFpFlatProperGroupoids S` along directed inverse limits
of affine schemes over `S`. -/
theorem exists_stage (S : Scheme.{u})
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (x : (pFpFlatProperGroupoids S).Fiber c.pt) :
    ∃ (i : I) (xi : (pFpFlatProperGroupoids S).Fiber (D.obj i)),
      IsIsomorphic (restrictObj xi (c.π.app i)) x :=
  sorry

/-- Fibre Hom-types of `pFpFlatProperGroupoids S` over a directed inverse limit
of affine schemes over `S` are the directed colimit of the corresponding stage
Hom-types. -/
theorem hom_isColimit (S : Scheme.{u})
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (i : I) (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i)) :
    Nonempty (IsColimit (homCocone S c x y)) :=
  sorry

end FpFlatProperGroupoids
end AlgebraicGeometry.AlgebraicSpace.Spaces
