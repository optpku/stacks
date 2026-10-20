module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Section
import StacksCheckRecall

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

/- Lemma 101.4.9 (1): let `f : X ⟶ T` be a morphism of algebraic stacks. Let
`s : T ⟶ X` be a morphism such that `s ≫ f` is 2-isomorphic to `𝟙 T`. Then
`s` is representable by algebraic spaces and locally of finite type. -/
@[stacks 050J] #check (AlgebraicGeometry.AlgebraicStack.locallyOfFiniteType_section :
  ∀ {S : Scheme.{u}} {X T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack T] (f : X ⟶ T) (s : T ⟶ X)
    (hs : s ≫ f ≅ 𝟙 T),
    Groupoids.Hom.LocallyOfFiniteType s)

/- A 2-section of a morphism of algebraic stacks is representable by algebraic
spaces. -/
#check (AlgebraicGeometry.AlgebraicStack.relativelyRepresentable_section :
  ∀ {S : Scheme.{u}}
    {X T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack T]
    (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f ≅ 𝟙 T),
    relativelyRepresentableByAlgebraicSpaces s)

/- Lemma 101.4.9 (2): let `f : X ⟶ T` be a morphism of algebraic stacks. Let
`s : T ⟶ X` be a morphism such that `s ≫ f` is 2-isomorphic to `𝟙 T`. If `f`
is DM, then `s` is unramified. -/
@[stacks 050J] #check (AlgebraicGeometry.AlgebraicStack.section_unramified :
  ∀ {S : Scheme.{u}} {X T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack T] (f : X ⟶ T) (s : T ⟶ X)
    (hs : s ≫ f ≅ 𝟙 T) [DM f],
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S) s)

/- Lemma 101.4.9 (3): let `f : X ⟶ T` be a morphism of algebraic stacks. Let
`s : T ⟶ X` be a morphism such that `s ≫ f` is 2-isomorphic to `𝟙 T`. If `f`
is quasi-DM, then `s` is locally quasi-finite. -/
@[stacks 050J] #check (AlgebraicGeometry.AlgebraicStack.section_locallyQuasiFinite :
  ∀ {S : Scheme.{u}} {X T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack T] (f : X ⟶ T) (s : T ⟶ X)
    (hs : s ≫ f ≅ 𝟙 T) [QuasiDM f],
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) s)

/- Lemma 101.4.9 (4): let `f : X ⟶ T` be a morphism of algebraic stacks. Let
`s : T ⟶ X` be a morphism such that `s ≫ f` is 2-isomorphic to `𝟙 T`. If `f`
is separated, then `s` is proper. -/
@[stacks 050J] #check (AlgebraicGeometry.AlgebraicStack.section_proper :
  ∀ {S : Scheme.{u}} {X T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack T] (f : X ⟶ T) (s : T ⟶ X)
    (hs : s ≫ f ≅ 𝟙 T) [Separated f],
    Groupoids.Hom.has (@AlgebraicSpace.Proper S) s)

/- Lemma 101.4.9 (5): let `f : X ⟶ T` be a morphism of algebraic stacks. Let
`s : T ⟶ X` be a morphism such that `s ≫ f` is 2-isomorphic to `𝟙 T`. If `f`
is quasi-separated, then `s` is quasi-compact and quasi-separated. -/
@[stacks 050J] #check (AlgebraicGeometry.AlgebraicStack.section_quasiCompact_quasiSeparated :
  ∀ {S : Scheme.{u}}
    {X T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack T]
    (f : X ⟶ T) (s : T ⟶ X) (hs : s ≫ f ≅ 𝟙 T) [QuasiSeparated f],
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) s ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) s)

/- A 2-section of a quasi-separated morphism of algebraic stacks is
quasi-compact. -/
#check (AlgebraicGeometry.AlgebraicStack.section_quasiCompact :
  ∀ {S : Scheme.{u}} {X T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack T] (f : X ⟶ T) (s : T ⟶ X)
    (hs : s ≫ f ≅ 𝟙 T) [QuasiSeparated f],
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) s)

/- A 2-section of a quasi-separated morphism of algebraic stacks is
quasi-separated. -/
#check (AlgebraicGeometry.AlgebraicStack.section_isQuasiSeparated :
  ∀ {S : Scheme.{u}} {X T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack T] (f : X ⟶ T) (s : T ⟶ X)
    (hs : s ≫ f ≅ 𝟙 T) [QuasiSeparated f],
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) s)

end AlgebraicGeometry.AlgebraicStack
