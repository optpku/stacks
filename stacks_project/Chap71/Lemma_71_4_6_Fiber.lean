module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap71.Lemma_71_4_1_Fiber

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

/-- A morphism of algebraic spaces has locally Noetherian fibres when, for
every point of the target, the equivalent conditions of Lemma 71.4.1 hold.
This is weaker than requiring every field-valued fibre to be locally
Noetherian. -/
class LocallyNoetherianFibers {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- For every point of `|Y|`, some field-valued representative has a locally
  Noetherian fibre. -/
  fiber_isLocallyNoetherian :
    ∀ y : Points Y, LocallyNoetherianFiber.existsField f y

namespace LocallyNoetherianFibers

/-- The fibres of `f` are locally Noetherian if and only if, for every point of
`|Y|`, the equivalent conditions `existsField` and `forallEtale` of
Lemma 71.4.1 hold. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    LocallyNoetherianFibers f ↔
      (∀ y : Points Y, LocallyNoetherianFiber.existsField f y) ∧
        (∀ y : Points Y, LocallyNoetherianFiber.forallEtale f y) :=
  sorry

/-- A morphism of algebraic spaces that is locally of finite type has locally
Noetherian fibres. -/
instance ofLocallyOfFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] : LocallyNoetherianFibers f where
  fiber_isLocallyNoetherian := sorry

end LocallyNoetherianFibers

end AlgebraicGeometry.AlgebraicSpace
