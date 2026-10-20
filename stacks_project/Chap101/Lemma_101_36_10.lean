/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.FlatUnramified
import StacksCheckRecall

/-!
# Characterizations of étale morphisms of algebraic stacks

A morphism of algebraic stacks is étale if and only if it is locally of finite
presentation, flat, and unramified, equivalently if and only if it is locally
of finite presentation, flat, and its relative 2-diagonal is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Etale

/- Lemma 101.36.10: Let `f : X ⟶ Y` be a morphism of algebraic stacks. The
following are equivalent: `Etale f`; `LocallyOfFinitePresentation f`, `Flat f`,
and `Unramified f`; and `LocallyOfFinitePresentation f`, `Flat f`, and
`Etale (Hom.diagonal f)`.

Stacks writes the diagonal of `f` as `Δ : X ⟶ X ×_Y X`; the Lean morphism is
`Hom.diagonal f : X ⟶ TwoFibreProduct.apex f f`. -/
@[stacks 0CJ1] #check
  (AlgebraicGeometry.AlgebraicStack.Etale.tfae_flat_unramified :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    List.TFAE
      [Etale f,
        LocallyOfFinitePresentation f ∧ Flat f ∧ Unramified f,
        LocallyOfFinitePresentation f ∧
          Flat f ∧ Etale (Hom.diagonal.{u + 1, u, u + 1} f)])

/- A morphism of algebraic stacks is étale if and only if it is locally of
finite presentation, flat, and unramified. -/
#check (AlgebraicGeometry.AlgebraicStack.Etale.iff_locallyOfFinitePresentation_flat_unramified :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Etale f ↔ LocallyOfFinitePresentation f ∧ Flat f ∧ Unramified f)

/- A morphism of algebraic stacks is étale if and only if it is locally of
finite presentation, flat, and its relative 2-diagonal is étale. -/
#check (AlgebraicGeometry.AlgebraicStack.Etale.iff_locallyOfFinitePresentation_flat_etale_diagonal :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Etale f ↔
      LocallyOfFinitePresentation f ∧
        Flat f ∧ Etale (Hom.diagonal.{u + 1, u, u + 1} f))

/- An étale morphism of algebraic stacks is locally of finite presentation. -/
#check (AlgebraicGeometry.AlgebraicStack.Etale.locallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Etale f],
    LocallyOfFinitePresentation f)

/- An étale morphism of algebraic stacks is flat. -/
#check (AlgebraicGeometry.AlgebraicStack.Etale.flat :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Etale f],
    Flat f)

/- A locally of finite presentation, flat, unramified morphism of algebraic
stacks is étale. -/
#check (AlgebraicGeometry.AlgebraicStack.Etale.of_locallyOfFinitePresentation_of_flat_of_unramified :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat f] [Unramified f],
    Etale f)

/- A locally of finite presentation, flat morphism of algebraic stacks whose
relative 2-diagonal is étale is étale. -/
#check (AlgebraicGeometry.AlgebraicStack.Etale.of_locallyOfFinitePresentation_of_flat_of_etale_diagonal :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat f]
    [Etale (Hom.diagonal.{u + 1, u, u + 1} f)],
    Etale f)

end AlgebraicGeometry.AlgebraicStack.Etale
