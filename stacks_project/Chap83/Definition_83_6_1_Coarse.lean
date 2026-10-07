module

public import stacks_project.Chap83.Definition_83_4_1_Quotient
public import stacks_project.Chap83.Definition_83_5_18_OrbitSpace

/-!
# Coarse quotients of a pre-relation

A morphism of algebraic spaces over a base is a coarse quotient of a pre-relation when it
is both a categorical quotient and an orbit space. When the base is a scheme and the
objects are schemes, the same two conditions in the category of schemes yield a coarse
quotient in schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace PreRelation

/-- A morphism `φ : U ⟶ X` over `B` is a coarse quotient of a pre-relation `P` when it is a
categorical quotient and an orbit space. -/
@[mk_iff]
class IsCoarseQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) : Prop where
  /-- The morphism is a categorical quotient of the pre-relation. -/
  isCategoricalQuotient : P.IsCategoricalQuotient φ
  /-- The morphism is an orbit space for the pre-relation. -/
  isOrbitSpace : P.IsOrbitSpace φ

/-- A categorical quotient that is also an orbit space is a coarse quotient. -/
instance instIsCoarseQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X} [P.IsCategoricalQuotient φ] [P.IsOrbitSpace φ] :
    P.IsCoarseQuotient φ where
  isCategoricalQuotient := inferInstance
  isOrbitSpace := inferInstance

/-- A coarse quotient is a categorical quotient and an orbit space. -/
theorem IsCoarseQuotient.spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) [P.IsCoarseQuotient φ] :
    P.IsCategoricalQuotient φ ∧ P.IsOrbitSpace φ :=
  sorry

/-- A morphism of schemes over `S` is a coarse quotient in schemes when it is a categorical
quotient in schemes and an orbit space. -/
@[mk_iff]
class IsCoarseQuotientInSchemes {S : Scheme.{u}}
    {U X : Over (ofOver (Over.mk (𝟙 S)))} (P : PreRelation U) (φ : U ⟶ X) : Prop where
  /-- The morphism is a categorical quotient in the category of schemes over `S`. -/
  isCategoricalQuotientInSchemes : P.IsCategoricalQuotientInSchemes φ
  /-- The morphism is an orbit space. -/
  isOrbitSpace : P.IsOrbitSpace φ

/-- A categorical quotient in schemes that is also an orbit space is a coarse quotient in
schemes. -/
instance instIsCoarseQuotientInSchemes {S : Scheme.{u}}
    {U X : Over (ofOver (Over.mk (𝟙 S)))} {P : PreRelation U} {φ : U ⟶ X}
    [P.IsCategoricalQuotientIn isScheme φ] [P.IsOrbitSpace φ] :
    P.IsCoarseQuotientInSchemes φ where
  isCategoricalQuotientInSchemes := inferInstance
  isOrbitSpace := inferInstance

/-- A coarse quotient in schemes is a categorical quotient in schemes and an orbit space. -/
theorem IsCoarseQuotientInSchemes.spec {S : Scheme.{u}}
    {U X : Over (ofOver (Over.mk (𝟙 S)))} (P : PreRelation U) (φ : U ⟶ X)
    [P.IsCoarseQuotientInSchemes φ] :
    P.IsCategoricalQuotientInSchemes φ ∧ P.IsOrbitSpace φ :=
  sorry

end PreRelation
end AlgebraicGeometry.AlgebraicSpace
