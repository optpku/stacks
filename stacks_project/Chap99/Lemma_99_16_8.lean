/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap99.Lemma_99_16_8_Groupoids

/-!
# Lemma 99.16.8

If `toBase B` is locally of finite presentation, then the projection
`p : Complexes f ⥤ Over S` is limit preserving in the sense of Artin's Axioms,
Definition 98.11.1. The Hom-universe of `Obj f` is `u + 1`, so this cannot be
stated as `AlgebraicGeometry.Groupoids.LimitPreserving` on `GroupoidsOver S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open CategoryTheory.Functor.Fiber
open AlgebraicGeometry.AlgebraicSpace.Complexes

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.16.8: in Situation 99.16.3 assume that `toBase B` is locally of finite
presentation. Then `p : Complexes f ⥤ Over S` is limit preserving in the sense of
Artin's Axioms, Definition 98.11.1: directed inverse limits of affine schemes
over `S` induce equivalences of fibre categories. -/
@[stacks 0DLJ]
theorem isLimitPreserving (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (toBase B)]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left) :
    (∀ x : (p f).Fiber c.pt, ∃ (i : I) (xi : (p f).Fiber (D.obj i)),
      IsIsomorphic (restrictObj xi (c.π.app i)) x) ∧
      ∀ (i : I) (x y : (p f).Fiber (D.obj i)),
        Nonempty (IsColimit (homCocone f c x y)) :=
  sorry

/-- Object descent for `p f` along directed inverse limits of affine schemes
over `S`. -/
theorem exists_stage (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (toBase B)]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (x : (p f).Fiber c.pt) :
    ∃ (i : I) (xi : (p f).Fiber (D.obj i)),
      IsIsomorphic (restrictObj xi (c.π.app i)) x :=
  sorry

/-- Fibre Hom-types of `p f` over a directed inverse limit of affine schemes
over `S` are the directed colimit of the corresponding stage Hom-types. -/
theorem hom_isColimit (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (toBase B)]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (i : I) (x y : (p f).Fiber (D.obj i)) :
    Nonempty (IsColimit (homCocone f c x y)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
