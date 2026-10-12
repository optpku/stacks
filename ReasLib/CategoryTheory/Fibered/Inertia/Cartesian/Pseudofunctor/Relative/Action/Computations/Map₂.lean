/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Action.Construction

/-!
# `2`-morphism computations for fibred relative inertia
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}

noncomputable section

namespace map₂

/-- Forgetting fibred structure from the relative-inertia action on a `2`-morphism recovers
its concrete based natural transformation. -/
@[simp]
theorem toBasedNatTrans {f g : S ⟶ T} (eta : f ⟶ g) :
    FiberedCategoryOver.toBasedNatTrans (map₂ eta) = basedNatTrans eta := sorry

/-- Evaluation of the fibred relative-inertia action on a `2`-morphism is its explicit
intertwining component. -/
@[simp]
theorem app {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    (FiberedCategoryOver.toNatTrans (map₂ eta)).app A = component eta A := sorry

/-- The arrow underlying a relative-inertia component is the left endpoint component of the
original pseudo-comma `2`-morphism. -/
@[simp]
theorem app.underlying {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans (map₂ eta)).app A) =
      (FiberedCategoryOver.toNatTrans
        (Bicategory.PseudoComma.left₂ eta)).app A.obj := sorry

/-- The arrow underlying the explicit component of a fibred relative-inertia `2`-morphism is
the left endpoint component of the original pseudo-comma `2`-morphism. -/
@[simp]
theorem component.underlying {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    CategoryTheory.RelativeInertia.hom (component eta A) =
      (FiberedCategoryOver.toNatTrans
        (Bicategory.PseudoComma.left₂ eta)).app A.obj := sorry

/-- The explicit component is vertical over the identity of the base object. -/
theorem component.isHomLift {f g : S ⟶ T} (eta : f ⟶ g)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    (FiberedCategoryOver.relativeInertia T.hom).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.relativeInertia S.hom).p.obj A))
      (component eta A) := sorry

/-- Naturality of the explicit relative-inertia component on total categories. -/
@[reassoc]
theorem component.naturality {f g : S ⟶ T} (eta : f ⟶ g)
    {A B : (FiberedCategoryOver.relativeInertia S.hom).total} (phi : A ⟶ B) :
    (FiberedCategoryOver.toFunctor (map f)).map phi ≫ component eta B =
      component eta A ≫ (FiberedCategoryOver.toFunctor (map g)).map phi := sorry

/-- The fibred relative-inertia action on pseudo-comma `2`-morphisms is natural on total
categories. -/
@[reassoc]
theorem naturality {f g : S ⟶ T} (eta : f ⟶ g)
    {A B : (FiberedCategoryOver.relativeInertia S.hom).total} (phi : A ⟶ B) :
    (FiberedCategoryOver.toFunctor (map f)).map phi ≫
        (FiberedCategoryOver.toNatTrans (map₂ eta)).app B =
      (FiberedCategoryOver.toNatTrans (map₂ eta)).app A ≫
        (FiberedCategoryOver.toFunctor (map g)).map phi := sorry

/-- Two induced fibred relative-inertia `2`-morphisms agree when all of their total-category
components agree. -/
theorem ext {f g : S ⟶ T} {eta theta : f ⟶ g}
    (h : ∀ A : (FiberedCategoryOver.relativeInertia S.hom).total,
      (FiberedCategoryOver.toNatTrans (map₂ eta)).app A =
        (FiberedCategoryOver.toNatTrans (map₂ theta)).app A) :
    map₂ eta = map₂ theta := sorry

end map₂

end

end FiberedCategoryOver.RelativeInertia.pseudoComma
end CategoryTheory
