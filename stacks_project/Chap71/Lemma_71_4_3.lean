module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_23_5

/-!
# Locally of finite type morphisms have locally Noetherian fibres

A morphism of algebraic spaces that is locally of finite type has locally
Noetherian fibres, realized as pullbacks along field-valued points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFiniteType

/-- Lemma 71.4.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally of finite type, then the fibres
of `f` are locally Noetherian. Here a fibre is the pullback of `f` along a
field-valued point of `Y`, matching Lemma 71.4.1(3) for every
`p : FieldValuedPoint Y`. -/
@[stacks 0CUY, instance]
theorem isLocallyNoetherian_fiber {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (p : FieldValuedPoint Y) :
    IsLocallyNoetherian (pullback f p.hom) :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace
