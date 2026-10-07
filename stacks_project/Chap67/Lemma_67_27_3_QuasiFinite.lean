module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite

/-!
# Quasi-finite morphisms of algebraic spaces

A morphism of algebraic spaces is quasi-finite when it is of finite type and
locally quasi-finite. This matches Stacks Definition 67.27.1 (3) through the
scheme-level meaning of locally quasi-finite, which already includes local
finite type on charts.

`FiniteType` and `LocallyQuasiFinite` both inherit an étale-square field
`of_etale`, so the class `extends FiniteType` and records
`LocallyQuasiFinite` as an instance field rather than a second parent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is quasi-finite if it is of finite type and
locally quasi-finite. -/
class QuasiFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop
    extends FiniteType f where
  /-- A quasi-finite morphism is locally quasi-finite. -/
  [locallyQuasiFinite : LocallyQuasiFinite f]

/-- A morphism of algebraic spaces is quasi-finite if and only if it is of
finite type and locally quasi-finite. -/
theorem quasiFinite_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : QuasiFinite f ↔ FiniteType f ∧ LocallyQuasiFinite f :=
  sorry

namespace QuasiFinite

/-- The identity morphism of an algebraic space is quasi-finite. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : QuasiFinite (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic spaces is quasi-finite. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIso f] : QuasiFinite f :=
  sorry

/-- A finite type locally quasi-finite morphism of algebraic spaces is
quasi-finite. -/
instance instOfFiniteTypeLocallyQuasiFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    [LocallyQuasiFinite f] : QuasiFinite f :=
  sorry

end QuasiFinite

end AlgebraicGeometry.AlgebraicSpace
