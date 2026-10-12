/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Canonical fibre morphisms of a self 2-fibre product

A morphism `φ : a ⟶ b` in `[U/R]` over `T` is represented by a switched object
`(b, a, α)` of the fibrewise categorical pullback of `fiberFunctor f T` with
itself. The associated fibre morphism is `α.inv : f(a) ⟶ f(b)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) {T : Over S}

/-- The object of `R` over `T` representing a morphism `φ : a ⟶ b` in `[U/R]`,
namely the switched triple `(b, a, α)` in the self categorical pullback of
`fiberFunctor f T`. -/
def ofSwitchedComparison (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a) :
    (fiberFunctor f T) ⊡ (fiberFunctor f T) :=
  ⟨b, a, α⟩

/-- The first component of a switched comparison triple is the target object. -/
theorem ofSwitchedComparison_fst (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a) :
    (ofSwitchedComparison f a b α).fst = b :=
  sorry

/-- The second component of a switched comparison triple is the source object. -/
theorem ofSwitchedComparison_snd (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a) :
    (ofSwitchedComparison f a b α).snd = a :=
  sorry

/-- The structural isomorphism of a switched comparison triple is the given
comparison `α : f(b) ≅ f(a)`. -/
theorem ofSwitchedComparison_iso (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a) :
    (ofSwitchedComparison f a b α).iso = α :=
  sorry

/-- The fibre morphism assigned by `f_can` to a morphism of `[U/R]`, represented
as an object of the self categorical pullback of `fiberFunctor f T`. -/
def canonicalHom (φ : (fiberFunctor f T) ⊡ (fiberFunctor f T)) :
    (fiberFunctor f T).obj φ.snd ⟶ (fiberFunctor f T).obj φ.fst :=
  φ.iso.inv

/-- `canonicalHom` is the inverse of the stored comparison isomorphism. -/
theorem canonicalHom_apply (φ : (fiberFunctor f T) ⊡ (fiberFunctor f T)) :
    canonicalHom f φ = φ.iso.inv :=
  sorry

end AlgebraicGeometry
