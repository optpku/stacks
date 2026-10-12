/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap99.Lemma_99_15_6_Hom

/-!
# Lemma 99.15.6

The projection `p S : Obj S ⥤ Over S` presents the stack
`Curves → Sch_fppf` and is limit preserving in the sense of Artin's Axioms,
Definition 98.11.1. The Hom-universe of `Obj S` is `u + 1`, so this cannot be
stated as `AlgebraicGeometry.Groupoids.LimitPreserving` on `GroupoidsOver S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open CategoryTheory.Functor.Fiber
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- Lemma 99.15.6: the stack `Curves → Sch_fppf`, presented by
`p S : Obj S ⥤ Over S` with `Over S` as `Sch_fppf`, is limit preserving in
the sense of Artin's Axioms, Definition 98.11.1: directed inverse limits of
affine schemes over `S` induce equivalences of fibre categories. -/
@[stacks 0D55]
theorem isLimitPreserving (S : Scheme.{u})
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left) :
    (∀ x : (p S).Fiber c.pt,
      ∃ (i : I) (xi : (p S).Fiber (D.obj i)),
        IsIsomorphic (restrictObj xi (c.π.app i)) x) ∧
      ∀ (i : I) (x y : (p S).Fiber (D.obj i)),
        Nonempty (IsColimit (homCocone S c x y)) :=
  sorry

/-- Object descent for `p S` along directed inverse limits of affine schemes
over `S`. -/
theorem exists_stage (S : Scheme.{u})
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (x : (p S).Fiber c.pt) :
    ∃ (i : I) (xi : (p S).Fiber (D.obj i)),
      IsIsomorphic (restrictObj xi (c.π.app i)) x :=
  sorry

/-- Fibre Hom-types of `p S` over a directed inverse limit of affine schemes
over `S` are the directed colimit of the corresponding stage Hom-types. -/
theorem hom_isColimit (S : Scheme.{u})
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (i : I) (x y : (p S).Fiber (D.obj i)) :
    Nonempty (IsColimit (homCocone S c x y)) :=
  sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
