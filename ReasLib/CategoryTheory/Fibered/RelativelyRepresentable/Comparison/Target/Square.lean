module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Target.Basic

/-!
# Square of the cone target comparison

This leaf packages the categorical-pullback target of a pseudo-pullback cone as a commutative
square and exposes the objectwise comparison isomorphisms identifying its two legs.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids.PseudoPullbackComparison

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The commutative square over `X.p` represented by `target P`. -/
@[stacks 0H2E "commutative square of a pseudo-pullback cone"]
noncomputable def target.square
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection) :
    CatCommSqOver X.p X.p P.pt.total :=
  (CategoricalPullback.toCatCommSqOver X.p X.p P.pt.total).obj
    (target P)

/-- The objectwise comparison between the first leg of `target.square P` and the underlying
left leg of `P`. The categorical-pullback lift retains this component definitionally. -/
noncomputable def target.square.fstIso.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((target.square P).fst).obj a ≅
      (FiberedCategoryOver.Groupoids.toFunctor P.fst).obj a :=
  Iso.refl _

/-- The explicit first-leg comparisons for `target.square P` are natural. -/
theorem target.square.fstIso.naturality
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    {a b : P.pt.total} (f : a ⟶ b) :
    (target.square P).fst.map f ≫ (target.square.fstIso.app P b).hom =
      (target.square.fstIso.app P a).hom ≫
        (FiberedCategoryOver.Groupoids.toFunctor P.fst).map f := sorry

/-- The first leg of `target.square P` is explicitly naturally isomorphic to the underlying
left leg of `P`. -/
@[stacks 0H2E "first-leg isomorphism of a pseudo-pullback cone target"]
noncomputable def target.square.fstIso
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection) :
    (target.square P).fst ≅
      FiberedCategoryOver.Groupoids.toFunctor P.fst :=
  NatIso.ofComponents
    (target.square.fstIso.app P)
    (fun f ↦ target.square.fstIso.naturality P f)

/-- The objectwise comparison between the second leg of `target.square P` and the underlying
right leg of `P`. The categorical-pullback lift retains this component definitionally. -/
noncomputable def target.square.sndIso.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((target.square P).snd).obj a ≅
      (FiberedCategoryOver.Groupoids.toFunctor P.snd).obj a :=
  Iso.refl _

/-- The explicit second-leg comparisons for `target.square P` are natural. -/
theorem target.square.sndIso.naturality
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    {a b : P.pt.total} (f : a ⟶ b) :
    (target.square P).snd.map f ≫ (target.square.sndIso.app P b).hom =
      (target.square.sndIso.app P a).hom ≫
        (FiberedCategoryOver.Groupoids.toFunctor P.snd).map f := sorry

/-- The second leg of `target.square P` is explicitly naturally isomorphic to the underlying
right leg of `P`. -/
@[stacks 0H2E "second-leg isomorphism of a pseudo-pullback cone target"]
noncomputable def target.square.sndIso
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection) :
    (target.square P).snd ≅
      FiberedCategoryOver.Groupoids.toFunctor P.snd :=
  NatIso.ofComponents
    (target.square.sndIso.app P)
    (fun f ↦ target.square.sndIso.naturality P f)

/-- The forward component of the first-leg comparison for `target.square` is its explicit
objectwise identity comparison. -/
@[simp]
theorem target.square.fstIso.hom.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    (target.square.fstIso P).hom.app a = (target.square.fstIso.app P a).hom := sorry

/-- The inverse component of the first-leg comparison for `target.square` is its explicit
objectwise identity comparison. -/
@[simp]
theorem target.square.fstIso.inv.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    (target.square.fstIso P).inv.app a = (target.square.fstIso.app P a).inv := sorry

/-- The forward component of the second-leg comparison for `target.square` is its explicit
objectwise identity comparison. -/
@[simp]
theorem target.square.sndIso.hom.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    (target.square.sndIso P).hom.app a = (target.square.sndIso.app P a).hom := sorry

/-- The inverse component of the second-leg comparison for `target.square` is its explicit
objectwise identity comparison. -/
@[simp]
theorem target.square.sndIso.inv.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    (target.square.sndIso P).inv.app a = (target.square.sndIso.app P a).inv := sorry

end

end FiberedCategoryOver.Groupoids.PseudoPullbackComparison

end CategoryTheory
