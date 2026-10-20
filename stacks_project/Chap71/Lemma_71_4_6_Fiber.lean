/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap71.Lemma_71_4_1_Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.FiniteType

/-!
# Locally Noetherian fibres of morphisms of algebraic spaces

A morphism of algebraic spaces has locally Noetherian fibres when, for every
point of the target, the equivalent conditions of Lemma 71.4.1 hold: some
field-valued representative has a locally Noetherian fibre, equivalently every
étale scheme chart through that point has locally Noetherian residue-field
fibre. Locally of finite type morphisms have this property. This does not
require every field-valued fibre to be locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.LocallyNoetherianFibers :
  {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.LocallyNoetherianFibers.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    LocallyNoetherianFibers f ↔
      (∀ y : Points Y, LocallyNoetherianFiber.existsField f y) ∧
        (∀ y : Points Y, LocallyNoetherianFiber.forallEtale f y))

#check (AlgebraicGeometry.AlgebraicSpace.LocallyNoetherianFibers.ofLocallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f], LocallyNoetherianFibers f)

end AlgebraicGeometry.AlgebraicSpace
