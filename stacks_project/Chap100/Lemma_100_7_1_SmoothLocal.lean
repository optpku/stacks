/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothLocal
public import stacks_project.Chap66.Lemma_66_7_1_EtaleLocal
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Smooth-local transfer for algebraic stacks

A smooth-local property of schemes transfers between surjective smooth scheme
atlases, arbitrary smooth scheme maps, and the corresponding algebraic-space
tests of an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- There exists a scheme `U` over `S` and a surjective smooth morphism
`GroupoidsOver.slice U ⟶ X` such that `U` has property `P`. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmooth :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X],
    Prop)

/- `existsSurjectiveSmooth P X` is the existence of a surjective smooth scheme
atlas with property `P`. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmooth_def :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X],
    existsSurjectiveSmooth P X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ P U.left)

namespace existsSurjectiveSmooth

/- A surjective smooth scheme atlas with property `P` witnesses
`existsSurjectiveSmooth P X`. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmooth.of :
  ∀ {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S} (p : GroupoidsOver.slice U ⟶ X)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p] (hP : P U.left),
    existsSurjectiveSmooth P X)

/- An algebraic stack satisfying `existsSurjectiveSmooth P X` admits a
surjective smooth scheme atlas with property `P`. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmooth.spec :
  ∀ {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (h : existsSurjectiveSmooth P X),
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ P U.left)

end existsSurjectiveSmooth

/- Every smooth morphism from a scheme `U` over `S` to `X` has `P U.left`. -/
#check (AlgebraicGeometry.AlgebraicStack.forallSmooth :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X],
    Prop)

/- `forallSmooth P X` is the statement that every smooth morphism from a scheme
to `X` has property `P` on the source. -/
#check (AlgebraicGeometry.AlgebraicStack.forallSmooth_def :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X],
    forallSmooth P X ↔
      ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p → P U.left)

namespace forallSmooth

/- The universal smooth-scheme condition witnesses `forallSmooth P X`. -/
#check (AlgebraicGeometry.AlgebraicStack.forallSmooth.of :
  ∀ {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    (h : ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p → P U.left),
    forallSmooth P X)

/- If `forallSmooth P X`, then every smooth morphism from a scheme `U` to `X`
has `P U.left`. -/
#check (AlgebraicGeometry.AlgebraicStack.forallSmooth.spec :
  ∀ {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (h : forallSmooth P X) {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (hp : Groupoids.Hom.Smooth p),
    P U.left)

end forallSmooth

/- There exists an algebraic space `U` over `S` and a surjective smooth morphism
`U.toGroupoids ⟶ X` such that `U` has property `P`. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmoothSpace :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X],
    Prop)

/- `existsSurjectiveSmoothSpace P X` is the existence of a surjective smooth
algebraic-space atlas with property `P`. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmoothSpace_def :
  ∀ {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) (X : GroupoidsOver S) [AlgebraicStack X],
    existsSurjectiveSmoothSpace P X ↔
      ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          AlgebraicSpace.existsSurjectiveEtale P U)

namespace existsSurjectiveSmoothSpace

/- A surjective smooth algebraic-space atlas with property `P` witnesses
`existsSurjectiveSmoothSpace P X`. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmoothSpace.of :
  ∀ {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : AlgebraicSpace S} (p : U.toGroupoids ⟶ X)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    (hP : AlgebraicSpace.existsSurjectiveEtale P U),
    existsSurjectiveSmoothSpace P X)

/- An algebraic stack satisfying `existsSurjectiveSmoothSpace P X` admits a
surjective smooth algebraic-space atlas with property `P`. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmoothSpace.spec :
  ∀ {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X]
    (h : existsSurjectiveSmoothSpace P X),
    ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicSpace.existsSurjectiveEtale P U)

end existsSurjectiveSmoothSpace

/- Every smooth morphism from an algebraic space `U` over `S` to `X` has
property `P` on `U`. -/
#check (AlgebraicGeometry.AlgebraicStack.forallSmoothSpace :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X],
    Prop)

/- `forallSmoothSpace P X` is the statement that every smooth morphism from an
algebraic space to `X` has property `P` on the source. -/
#check (AlgebraicGeometry.AlgebraicStack.forallSmoothSpace_def :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X],
    forallSmoothSpace P X ↔
      ∀ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
        Groupoids.Hom.Smooth p → AlgebraicSpace.existsSurjectiveEtale P U)

namespace forallSmoothSpace

/- The universal smooth algebraic-space condition witnesses
`forallSmoothSpace P X`. -/
#check (AlgebraicGeometry.AlgebraicStack.forallSmoothSpace.of :
  ∀ {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    (h : ∀ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
      Groupoids.Hom.Smooth p → AlgebraicSpace.existsSurjectiveEtale P U),
    forallSmoothSpace P X)

/- If `forallSmoothSpace P X`, then every smooth morphism from an algebraic
space `U` to `X` has property `P` on `U`. -/
#check (AlgebraicGeometry.AlgebraicStack.forallSmoothSpace.spec :
  ∀ {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] (h : forallSmoothSpace P X)
    {U : AlgebraicSpace S} (p : U.toGroupoids ⟶ X)
    (hp : Groupoids.Hom.Smooth p),
    AlgebraicSpace.existsSurjectiveEtale P U)

end forallSmoothSpace

end AlgebraicGeometry.AlgebraicStack
