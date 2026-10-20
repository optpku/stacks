/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup.Pullback
import StacksCheckRecall

/-!
# Injectivity of field-valued morphisms in a cartesian square

If a morphism of algebraic stacks induces isomorphisms of automorphism groups
at points, then in any 2-cartesian square the pairing of Hom-groupoids from
`Spec(k)` into the two legs is injective on isomorphism classes.
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

/- Lemma 101.45.6: in a cartesian diagram of algebraic stacks, if `f`
induces an isomorphism between automorphism groups at points
(Remark 101.19.5), then
`Mor(Spec(k), X') ⟶ Mor(Spec(k), Y') × Mor(Spec(k), X)`
is injective on isomorphism classes for any field `k`.

Cartesianness is `IsBilimit` of an explicit `PseudoPullbackCone f g`, the
product order is `(c.snd, c.fst)`, and `Mor(Spec(k), -)` is Hom from
`GroupoidsOver.slice (Over.mk σ)`. -/
@[stacks 0DUC]
#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoAt.homIsoClasses_injective :
    ∀ {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : PseudoPullbackCone f g)
    [AlgebraicStack c.pt] (hc : c.IsBilimit)
    (hf : ∀ x : |X|, IsIsoAt f x) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S)
    {φ ψ : GroupoidsOver.slice (Over.mk σ) ⟶ c.pt},
    Nonempty (φ ≫ c.snd ≅ ψ ≫ c.snd) →
      Nonempty (φ ≫ c.fst ≅ ψ ≫ c.fst) → Nonempty (φ ≅ ψ))

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoAt.fiberIsoClasses_injective :
    ∀ {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : PseudoPullbackCone f g)
    [AlgebraicStack c.pt] (hc : c.IsBilimit)
    (hf : ∀ x : |X|, IsIsoAt f x) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S),
    Function.Injective fun a ↦
      ((fiberFunctor c.snd (Over.mk σ)).isoClassesMap a,
        (fiberFunctor c.fst (Over.mk σ)).isoClassesMap a))

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoAt.homIsoClasses_injective_twoFibreProduct :
    ∀ {S : Scheme.{u}}
    {X Y Y' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Y'] (f : X ⟶ Y) (g : Y' ⟶ Y)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    (hf : ∀ x : |X|, IsIsoAt f x) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S)
    {φ ψ : GroupoidsOver.slice (Over.mk σ) ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g},
    Nonempty
        (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g ≅
          ψ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) →
      Nonempty
        (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g ≅
          ψ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) →
      Nonempty (φ ≅ ψ))

end IsIsoAt

end automorphismGroup

end AlgebraicGeometry.AlgebraicStack
