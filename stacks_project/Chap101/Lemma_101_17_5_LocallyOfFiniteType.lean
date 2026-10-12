/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap101.Lemma_101_25_5_Flat

/-!
# Locally of finite type for morphisms of algebraic stacks

A morphism of algebraic stacks is locally of finite type when some smooth
algebraic-space presentation square with surjective source atlas has
locally-of-finite-type top arrow, parallel to `AlgebraicStack.Flat`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks over `S` is locally of finite
type if some commutative square with algebraic-space vertices, smooth
vertical arrows, and surjective source atlas has locally-of-finite-type
top arrow. -/
class LocallyOfFiniteType {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- There is a smooth presentation of `f` by algebraic spaces whose source
  atlas is surjective and whose top arrow is locally of finite type. -/
  exists_surjective_smooth_presentation :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFiniteType h

/-- A morphism of algebraic stacks is locally of finite type if and only
if it admits a smooth algebraic-space presentation with surjective source atlas
and locally-of-finite-type top arrow. -/
theorem locallyOfFiniteType_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧
          AlgebraicSpace.LocallyOfFiniteType h :=
  sorry

namespace LocallyOfFiniteType

/-- The identity morphism of an algebraic stack is locally of finite type. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    LocallyOfFiniteType (𝟙 X) :=
  sorry

/-- A locally-of-finite-type morphism of algebraic stacks admits a smooth
algebraic-space presentation with surjective source atlas and
locally-of-finite-type top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFiniteType h :=
  sorry

/-- A morphism of algebraic spaces that is locally of finite type induces a
1-morphism of algebraic stacks that is locally of finite type. -/
instance of_toGroupoids {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.LocallyOfFiniteType f] :
    LocallyOfFiniteType (AlgebraicSpace.toGroupoids.map f) :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicStack
