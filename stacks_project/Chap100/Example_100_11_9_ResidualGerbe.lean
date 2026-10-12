/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import stacks_project.Chap68.Lemma_68_13_12_ResidualSpace
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian

/-!
# Residual gerbes of algebraic stacks

A residual gerbe of an algebraic stack `X` at a point `x` is a monomorphism
`Z ⟶ X` from a reduced, locally Noetherian singleton algebraic stack whose
image on points is `{x}`. The scheme-theoretic example is the residue-field
inclusion `Spec (U.left.residueField u) ⟶ U.left`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A monomorphism `ι : Z ⟶ X` of algebraic stacks is a residual gerbe of `X` at
`x` when `Z` is reduced, locally Noetherian, and a singleton, and the image of
`Points.map ι` is `{x}`. -/
class IsResidualGerbe {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X) : Prop where
  /-- A residual-gerbe morphism is a monomorphism of groupoid fibrations. -/
  [mono : Groupoids.Hom.Mono ι]
  /-- The residual gerbe is reduced. -/
  [isReduced : IsReduced Z]
  /-- The residual gerbe is locally Noetherian. -/
  [isLocallyNoetherian : IsLocallyNoetherian Z]
  /-- The residual gerbe is a singleton. -/
  [subsingleton_points : Subsingleton (Points Z)]
  /-- The image of `Points.map ι` is the singleton `{x}`. -/
  image_eq : Set.range (Points.map ι) = {x}

namespace IsResidualGerbe

/-- A residual-gerbe monomorphism is a monomorphism from a reduced, locally
Noetherian singleton algebraic stack whose image on points is `{x}`. -/
theorem spec {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X} [IsResidualGerbe ι x] :
    Groupoids.Hom.Mono ι ∧ IsReduced Z ∧ IsLocallyNoetherian Z ∧
      Subsingleton (Points Z) ∧ Set.range (Points.map ι) = {x} :=
  sorry

/-- A morphism of algebraic stacks is a residual gerbe at `x` if and only if it
is a monomorphism from a reduced, locally Noetherian singleton whose image on
points is `{x}`. -/
theorem iff {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X) :
    IsResidualGerbe ι x ↔
      Groupoids.Hom.Mono ι ∧ IsReduced Z ∧ IsLocallyNoetherian Z ∧
        Subsingleton (Points Z) ∧ Set.range (Points.map ι) = {x} :=
  sorry

/-- The identity of a reduced, locally Noetherian singleton algebraic stack is a
residual gerbe at its unique point. -/
instance id {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    [IsReduced Z] [IsLocallyNoetherian Z] [Subsingleton (Points Z)]
    {x : Points Z} : IsResidualGerbe (𝟙 Z) x :=
  sorry

/-- Every point of a residual gerbe maps to the marked point of the target. -/
theorem map_eq {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X} [IsResidualGerbe ι x]
    (z : Points Z) : Points.map ι z = x :=
  sorry

/-- The image of a residual-space monomorphism of algebraic spaces is a residual
gerbe of the associated algebraic stacks. -/
theorem ofResidualSpace {S : Scheme.{u}} {X Z : AlgebraicSpace S} {ι : Z ⟶ X}
    {x : AlgebraicSpace.Points X} [AlgebraicSpace.IsResidualSpace ι x]
    (z : Points Z.toGroupoids) :
    IsResidualGerbe (AlgebraicSpace.toGroupoids.map ι)
      (Points.map (AlgebraicSpace.toGroupoids.map ι) z) :=
  sorry

end IsResidualGerbe

/-- The residue-field inclusion `U.left.fromSpecResidueField u` as a 1-morphism
of slice algebraic stacks over `S`. -/
def residueFieldι {S : Scheme.{u}} {U : Over S} (u : U.left) :
    GroupoidsOver.slice (Over.mk (U.left.fromSpecResidueField u ≫ U.hom)) ⟶
      GroupoidsOver.slice U :=
  overMap (Over.homMk (U.left.fromSpecResidueField u))

/-- `residueFieldι u` is `overMap` of `Over.homMk` of the residue-field map at
`u`. -/
theorem residueFieldι_eq {S : Scheme.{u}} {U : Over S} (u : U.left) :
    residueFieldι u = overMap (Over.homMk (U.left.fromSpecResidueField u)) :=
  sorry

/-- The point of `GroupoidsOver.slice U` represented by the residue-field
inclusion at `u`. -/
def residueFieldPoint {S : Scheme.{u}} {U : Over S} (u : U.left) :
    Points (GroupoidsOver.slice U) :=
  Points.mk
    (FieldValuedPoint.of (U.left.residueField u)
      (U.left.fromSpecResidueField u ≫ U.hom) (residueFieldι u))

/-- `residueFieldPoint u` is the class of the field-valued point given by
`residueFieldι u`. -/
theorem residueFieldPoint_eq {S : Scheme.{u}} {U : Over S} (u : U.left) :
    residueFieldPoint u =
      Points.mk
        (FieldValuedPoint.of (U.left.residueField u)
          (U.left.fromSpecResidueField u ≫ U.hom) (residueFieldι u)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
