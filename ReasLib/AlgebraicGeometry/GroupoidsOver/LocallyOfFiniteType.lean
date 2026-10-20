module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty

/-!
# Locally of finite type morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is locally of finite type when every
representing morphism of algebraic spaces `Fy ⟶ ofOver U` is locally of finite
type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S` is locally of
finite type when it is representable by algebraic spaces and every representing
morphism `fy : Fy ⟶ ofOver U` is a locally of finite type morphism of algebraic
spaces. -/
class LocallyOfFiniteType {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is locally of finite type. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.LocallyOfFiniteType fy

namespace LocallyOfFiniteType

/-- The identity 1-morphism of a category fibred in groupoids is locally of
finite type. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} : LocallyOfFiniteType (𝟙 X) :=
  sorry

/-- A representing morphism of algebraic spaces for a locally of finite type
1-morphism is locally of finite type. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {U : Over S} (y : GroupoidsOver.slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.LocallyOfFiniteType fy :=
  sorry

/-- A locally of finite type 1-morphism is representable by algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- A 1-morphism is locally of finite type if and only if it is representable by
algebraic spaces and every representing morphism of algebraic spaces is locally
of finite type. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy → AlgebraicSpace.LocallyOfFiniteType fy :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.Groupoids.Hom
