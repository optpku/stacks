module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses

/-!
# Stabilizer-preserving morphisms and pullback injectivity

The projections of a cartesian square of algebraic stacks jointly distinguish
isomorphism classes over each field when the original morphism preserves
automorphism groups.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace automorphismGroup

namespace IsIsoAt

/-- In a cartesian square of algebraic stacks, a stabilizer-preserving
morphism makes the two projections jointly injective on isomorphism classes
of morphisms from every field spectrum. The projection order is
`(c.snd, c.fst)`. -/
@[stacks 0DUC]
theorem homIsoClasses_injective {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : PseudoPullbackCone f g)
    [AlgebraicStack c.pt] (hc : c.IsBilimit)
    (hf : ∀ x : |X|, IsIsoAt f x) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S)
    {φ ψ : GroupoidsOver.slice (Over.mk σ) ⟶ c.pt} :
    Nonempty (φ ≫ c.snd ≅ ψ ≫ c.snd) →
      Nonempty (φ ≫ c.fst ≅ ψ ≫ c.fst) → Nonempty (φ ≅ ψ) :=
  sorry

/-- The pairing of fibrewise isomorphism-class maps of the two cone
projections is injective on fibres over `Spec(k)`. -/
theorem fiberIsoClasses_injective {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : PseudoPullbackCone f g)
    [AlgebraicStack c.pt] (hc : c.IsBilimit)
    (hf : ∀ x : |X|, IsIsoAt f x) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) :
    Function.Injective fun a ↦
      ((fiberFunctor c.snd (Over.mk σ)).isoClassesMap a,
        (fiberFunctor c.fst (Over.mk σ)).isoClassesMap a) :=
  sorry

/-- Specialization of Hom-level injectivity to the chosen 2-fibre product of
`f` and `g`. -/
theorem homIsoClasses_injective_twoFibreProduct {S : Scheme.{u}}
    {X Y Y' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Y'] (f : X ⟶ Y) (g : Y' ⟶ Y)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    (hf : ∀ x : |X|, IsIsoAt f x) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S)
    {φ ψ : GroupoidsOver.slice (Over.mk σ) ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g} :
    Nonempty
        (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g ≅
          ψ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) →
      Nonempty
        (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g ≅
          ψ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) →
      Nonempty (φ ≅ ψ) :=
  sorry

end IsIsoAt

end automorphismGroup

end AlgebraicGeometry.AlgebraicStack
