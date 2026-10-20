module

public import stacks_project.Chap87.Lemma_87_25_2_Surjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 87.24.1 (1): a morphism `f : Y ⟶ X` of formal algebraic spaces over a
scheme `S` is locally of finite type if it is representable by algebraic spaces
and is locally of finite type in the sense of Bootstrap, Definition 80.4.1, i.e.
the Bootstrap transfer `relativeAlgebraicSpaces (@AlgebraicSpace.LocallyOfFiniteType S)`. -/
@[stacks 0AM4] #check AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Definition 87.24.1 (2): a morphism `f : Y ⟶ X` of formal algebraic spaces over a
scheme `S` is of finite type if it is locally of finite type and quasi-compact
in the sense of Definition 87.17.4, i.e. the induced map of algebraic-space
reductions `mapReduction f` is a quasi-compact morphism of algebraic spaces. -/
@[stacks 0AM4, mk_iff]
class IsFiniteType {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) : Prop
    extends LocallyOfFiniteType f where
  /-- The induced map of reductions is a quasi-compact morphism of algebraic
  spaces. -/
  map_quasiCompact : AlgebraicSpace.QuasiCompact (mapReduction f)

namespace IsFiniteType

/-- The identity morphism of a formal algebraic space is of finite type. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X] : IsFiniteType (𝟙 X) :=
  sorry

/-- A morphism of formal algebraic spaces is of finite type when it is locally
of finite type and the induced map of algebraic-space reductions is
quasi-compact. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [IsFiniteType f] :
    LocallyOfFiniteType f ∧ AlgebraicSpace.QuasiCompact (mapReduction f) :=
  sorry

end IsFiniteType

end AlgebraicGeometry.FormalAlgebraicSpace
