module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe

/-!
# Residual gerbes of algebraic stacks

The residual-gerbe predicate and the canonical residue-field constructions are
provided by the shared residual-gerbe module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe :
  ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z],
    (Z ⟶ X) → Points X → Prop)

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.spec :
  ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X} [IsResidualGerbe ι x],
    Groupoids.Hom.Mono ι ∧ IsReduced Z ∧ IsLocallyNoetherian Z ∧
      Subsingleton (Points Z) ∧ Set.range (Points.map ι) = {x})

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.iff :
  ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X),
    IsResidualGerbe ι x ↔
      Groupoids.Hom.Mono ι ∧ IsReduced Z ∧ IsLocallyNoetherian Z ∧
        Subsingleton (Points Z) ∧ Set.range (Points.map ι) = {x})

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.id :
  ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    [IsReduced Z] [IsLocallyNoetherian Z] [Subsingleton (Points Z)]
    {x : Points Z}, IsResidualGerbe (𝟙 Z) x)

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.map_eq :
  ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X} [IsResidualGerbe ι x]
    (z : Points Z), Points.map ι z = x)

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.ofResidualSpace :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} {ι : Z ⟶ X}
    (x : AlgebraicSpace.Points X) [AlgebraicSpace.IsResidualSpace ι x]
    (z : Points Z.toGroupoids),
    IsResidualGerbe (AlgebraicSpace.toGroupoids.map ι)
      (Points.map (AlgebraicSpace.toGroupoids.map ι) z))

#check (AlgebraicGeometry.AlgebraicStack.residueFieldι :
  ∀ {S : Scheme.{u}} {U : Over S} (u : U.left),
    GroupoidsOver.slice (Over.mk (U.left.fromSpecResidueField u ≫ U.hom)) ⟶
      GroupoidsOver.slice U)

#check (AlgebraicGeometry.AlgebraicStack.residueFieldι_eq :
  ∀ {S : Scheme.{u}} {U : Over S} (u : U.left),
    residueFieldι u = overMap (Over.homMk (U.left.fromSpecResidueField u)))

#check (AlgebraicGeometry.AlgebraicStack.residueFieldPoint :
  ∀ {S : Scheme.{u}} {U : Over S}, U.left → Points (GroupoidsOver.slice U))

#check (AlgebraicGeometry.AlgebraicStack.residueFieldPoint_eq :
  ∀ {S : Scheme.{u}} {U : Over S} (u : U.left),
    residueFieldPoint u =
      Points.mk
        (FieldValuedPoint.of (U.left.residueField u)
          (U.left.fromSpecResidueField u ≫ U.hom) (residueFieldι u)))

end AlgebraicGeometry.AlgebraicStack
