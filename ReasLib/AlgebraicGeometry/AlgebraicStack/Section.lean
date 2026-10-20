module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFiniteType

/-!
# Sections of morphisms of algebraic stacks

A 2-section of a morphism of algebraic stacks is representable by algebraic
spaces and locally of finite type. It is unramified if the morphism is DM,
locally quasi-finite if the morphism is quasi-DM, proper if the morphism is
separated, and quasi-compact and quasi-separated if the morphism is
quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A 2-section of a morphism of algebraic stacks is representable by algebraic
spaces and locally of finite type. -/
theorem locallyOfFiniteType_section {S : Scheme.{u}} {X T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack T] (f : X ⟶ T) (s : T ⟶ X)
    (hs : s ≫ f ≅ 𝟙 T) :
    Groupoids.Hom.LocallyOfFiniteType s :=
  sorry

/-- A 2-section of a morphism of algebraic stacks is representable by algebraic
spaces. -/
theorem relativelyRepresentable_section {S : Scheme.{u}}
    {X T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack T]
    (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f ≅ 𝟙 T) :
    relativelyRepresentableByAlgebraicSpaces s :=
  (locallyOfFiniteType_section f s hs).representable

/-- A 2-section of a DM morphism of algebraic stacks is unramified. -/
theorem section_unramified {S : Scheme.{u}} {X T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack T] (f : X ⟶ T) (s : T ⟶ X)
    (hs : s ≫ f ≅ 𝟙 T) [DM f] :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S) s :=
  sorry

/-- A 2-section of a quasi-DM morphism of algebraic stacks is locally
quasi-finite. -/
theorem section_locallyQuasiFinite {S : Scheme.{u}} {X T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack T] (f : X ⟶ T) (s : T ⟶ X)
    (hs : s ≫ f ≅ 𝟙 T) [QuasiDM f] :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) s :=
  sorry

/-- A 2-section of a separated morphism of algebraic stacks is proper. -/
theorem section_proper {S : Scheme.{u}} {X T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack T] (f : X ⟶ T) (s : T ⟶ X)
    (hs : s ≫ f ≅ 𝟙 T) [Separated f] :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S) s :=
  sorry

/-- A 2-section of a quasi-separated morphism of algebraic stacks is
quasi-compact and quasi-separated. -/
theorem section_quasiCompact_quasiSeparated {S : Scheme.{u}}
    {X T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack T]
    (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f ≅ 𝟙 T) [QuasiSeparated f] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) s ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) s :=
  sorry

/-- A 2-section of a quasi-separated morphism of algebraic stacks is
quasi-compact. -/
theorem section_quasiCompact {S : Scheme.{u}} {X T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack T] (f : X ⟶ T) (s : T ⟶ X)
    (hs : s ≫ f ≅ 𝟙 T) [QuasiSeparated f] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) s :=
  (section_quasiCompact_quasiSeparated f s hs).1

/-- A 2-section of a quasi-separated morphism of algebraic stacks is
quasi-separated. -/
theorem section_isQuasiSeparated {S : Scheme.{u}} {X T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack T] (f : X ⟶ T) (s : T ⟶ X)
    (hs : s ≫ f ≅ 𝟙 T) [QuasiSeparated f] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) s :=
  (section_quasiCompact_quasiSeparated f s hs).2

end AlgebraicGeometry.AlgebraicStack
