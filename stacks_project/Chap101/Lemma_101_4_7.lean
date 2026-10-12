/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_11_2_LocallyOfFiniteType
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Lemma_101_4_7_MapDesc

/-!
# Induced morphism of fibre products after a map of algebraic stacks

For morphisms `f : X ⟶ Z`, `g : Y ⟶ Z`, and `h : Z ⟶ T` of algebraic
stacks, the comparison `mapDesc f g h : X ×_Z Y ⟶ X ×_T Y` is representable
by algebraic spaces and locally of finite type, and inherits quasi-separated,
separated, unramified, locally quasi-finite, proper, and quasi-compact
properties from the relative 2-diagonal of `h` or from `h` itself.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LocallyOfFiniteType

/-- Lemma 101.4.7 (1): let `f : X ⟶ Z`, `g : Y ⟶ Z` and `h : Z ⟶ T` be
morphisms of algebraic stacks. The induced morphism
`mapDesc f g h : X ×_Z Y ⟶ X ×_T Y` is representable by algebraic spaces and
locally of finite type. -/
@[stacks 050H]
instance mapDesc {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    LocallyOfFiniteType (AlgebraicStack.mapDesc f g h) :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.Groupoids.Hom

namespace AlgebraicGeometry.AlgebraicStack

/-- The comparison `mapDesc f g h` is representable by algebraic spaces. -/
theorem relativelyRepresentable_mapDesc {S : Scheme.{u}}
    {X Y Z T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [AlgebraicStack T] (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) :
    relativelyRepresentableByAlgebraicSpaces (mapDesc f g h) :=
  sorry

/-- Lemma 101.4.7 (2): let `f : X ⟶ Z`, `g : Y ⟶ Z` and `h : Z ⟶ T` be
morphisms of algebraic stacks. If the relative 2-diagonal `Hom.diagonal h` is
quasi-separated, then `mapDesc f g h` is quasi-separated. -/
@[stacks 050H]
theorem mapDesc_quasiSeparated {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (h_quasiSeparated :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} h)) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (mapDesc f g h) :=
  sorry

/-- Lemma 101.4.7 (3): let `f : X ⟶ Z`, `g : Y ⟶ Z` and `h : Z ⟶ T` be
morphisms of algebraic stacks. If the relative 2-diagonal `Hom.diagonal h` is
separated, then `mapDesc f g h` is separated. -/
@[stacks 050H]
theorem mapDesc_separated {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (h_separated :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (Hom.diagonal.{u + 1, u, u + 1} h)) :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S) (mapDesc f g h) :=
  sorry

/-- Lemma 101.4.7 (4): let `f : X ⟶ Z`, `g : Y ⟶ Z` and `h : Z ⟶ T` be
morphisms of algebraic stacks. If `h` is DM, then `mapDesc f g h` is
unramified. -/
@[stacks 050H]
theorem mapDesc_unramified {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [DM h] :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S) (mapDesc f g h) :=
  sorry

/-- Lemma 101.4.7 (5): let `f : X ⟶ Z`, `g : Y ⟶ Z` and `h : Z ⟶ T` be
morphisms of algebraic stacks. If `h` is quasi-DM, then `mapDesc f g h` is
locally quasi-finite. -/
@[stacks 050H]
theorem mapDesc_locallyQuasiFinite {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiDM h] :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) (mapDesc f g h) :=
  sorry

/-- Lemma 101.4.7 (6): let `f : X ⟶ Z`, `g : Y ⟶ Z` and `h : Z ⟶ T` be
morphisms of algebraic stacks. If `h` is separated, then `mapDesc f g h` is
proper. -/
@[stacks 050H]
theorem mapDesc_proper {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [Separated h] :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S) (mapDesc f g h) :=
  sorry

/-- Lemma 101.4.7 (7): let `f : X ⟶ Z`, `g : Y ⟶ Z` and `h : Z ⟶ T` be
morphisms of algebraic stacks. If `h` is quasi-separated, then `mapDesc f g h`
is quasi-compact and quasi-separated. -/
@[stacks 050H]
theorem mapDesc_quasiCompact_quasiSeparated {S : Scheme.{u}}
    {X Y Z T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [AlgebraicStack T] (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) [QuasiSeparated h] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) (mapDesc f g h) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (mapDesc f g h) :=
  sorry

/-- The comparison `mapDesc f g h` along a quasi-separated morphism is
quasi-compact. -/
theorem mapDesc_quasiCompact {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) (mapDesc f g h) :=
  sorry

/-- The comparison `mapDesc f g h` along a quasi-separated morphism is
quasi-separated. -/
theorem mapDesc_isQuasiSeparated {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (mapDesc f g h) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
