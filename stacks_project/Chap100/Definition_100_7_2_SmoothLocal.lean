module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothLocal
public import stacks_project.Chap100.Lemma_100_7_1

/-!
# Smooth-local scheme properties of algebraic stacks

A property of schemes that is local in the smooth topology descends to
algebraic stacks by testing it on a surjective smooth scheme atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocal :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.bigSmoothPrecoverage] (X : GroupoidsOver S)
    [AlgebraicStack X],
    Prop)

#check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocal_def :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.bigSmoothPrecoverage] (X : GroupoidsOver S)
    [AlgebraicStack X],
    hasSmoothLocal P X ↔ existsSurjectiveSmooth P X)

#check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocal.of :
  ∀ {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}}
    [P.IsLocal Scheme.bigSmoothPrecoverage] {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S} (p : GroupoidsOver.slice U ⟶ X)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p] (hP : P U.left),
    hasSmoothLocal P X)

#check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocal.spec :
  ∀ {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}}
    [P.IsLocal Scheme.bigSmoothPrecoverage] {X : GroupoidsOver S}
    [AlgebraicStack X] (h : hasSmoothLocal P X),
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ P U.left)

#check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocal_iff_forallSmooth :
  ∀ {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (X : GroupoidsOver S) [AlgebraicStack X],
    hasSmoothLocal P X ↔ forallSmooth P X)

#check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocal_iff_existsSurjectiveSmoothSpace :
  ∀ {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (X : GroupoidsOver S) [AlgebraicStack X],
    hasSmoothLocal P X ↔ existsSurjectiveSmoothSpace P X)

#check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocal_iff_forallSmoothSpace :
  ∀ {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (X : GroupoidsOver S) [AlgebraicStack X],
    hasSmoothLocal P X ↔ forallSmoothSpace P X)

#check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocal_slice :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.bigSmoothPrecoverage] (U : Over S),
    hasSmoothLocal P (GroupoidsOver.slice U) ↔ P U.left)

#check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocal_toGroupoids :
  ∀ {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    [P.IsLocal Scheme.etalePrecoverage] (F : AlgebraicSpace S),
    hasSmoothLocal P F.toGroupoids ↔ AlgebraicSpace.hasEtaleLocal P F)

end AlgebraicGeometry.AlgebraicStack
