/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic

/-!
# Inverse comparisons in fibrewise categorical pullbacks

A switched comparison triple `(b, a, α)` stores an isomorphism from the image
of `b` to the image of `a`. Its inverse is a morphism from the image of `a`
to the image of `b`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) {T : Over S}

/-- The switched comparison triple `(b, a, α)` in the self categorical pullback
of the functor induced by `f` on the fibre over `T`. -/
def ofSwitchedComparison (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a) :
    (fiberFunctor f T) ⊡ (fiberFunctor f T) :=
  ⟨b, a, α⟩

/-- The first component of a switched comparison triple is `b`. -/
theorem ofSwitchedComparison_fst (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a) :
    (ofSwitchedComparison f a b α).fst = b :=
  sorry

/-- The second component of a switched comparison triple is `a`. -/
theorem ofSwitchedComparison_snd (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a) :
    (ofSwitchedComparison f a b α).snd = a :=
  sorry

/-- The structural isomorphism of a switched comparison triple is the supplied
comparison from the image of `b` to the image of `a`. -/
theorem ofSwitchedComparison_iso (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a) :
    (ofSwitchedComparison f a b α).iso = α :=
  sorry

/-- The inverse structural comparison of an object of the fibrewise self
categorical pullback, directed from the image of its second component to the
image of its first component. -/
def canonicalHom (φ : (fiberFunctor f T) ⊡ (fiberFunctor f T)) :
    (fiberFunctor f T).obj φ.snd ⟶ (fiberFunctor f T).obj φ.fst :=
  φ.iso.inv

/-- The inverse structural comparison is the inverse of the stored isomorphism. -/
theorem canonicalHom_apply (φ : (fiberFunctor f T) ⊡ (fiberFunctor f T)) :
    canonicalHom f φ = φ.iso.inv :=
  sorry

/-- The inverse structural comparison of the switched triple `(b, a, α)` is
`α.inv`, a morphism from the image of `a` to the image of `b`. -/
@[stacks 04TG]
theorem canonicalHom_eq_inv {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    {T : Over S} (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a) :
    canonicalHom f (ofSwitchedComparison f a b α) = α.inv :=
  sorry

end AlgebraicGeometry
