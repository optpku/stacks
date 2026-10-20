/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothLocal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import stacks_project.Chap66.Definition_66_7_2
public import stacks_project.Chap100.Lemma_100_7_1_SmoothLocal

/-!
# Smooth-local scheme properties of algebraic stacks

A property of schemes that is local in the smooth topology may be tested on
any, or some surjective, smooth morphism to an algebraic stack from a scheme
or from an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 100.7.1 (1): let `P` be a property of schemes which is local in the
smooth topology, and let `X` be an algebraic stack. There exists a scheme `U`
and a surjective smooth morphism `U ⟶ X` with `P U.left` if and only if every
smooth morphism `U ⟶ X` from a scheme has `P U.left`. -/
@[stacks 04YF]
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmooth_iff_forallSmooth :
  ∀ {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (X : GroupoidsOver S) [AlgebraicStack X],
    existsSurjectiveSmooth P X ↔ forallSmooth P X)

/- Lemma 100.7.1 (2): let `P` be a property of schemes which is local in the
smooth topology, and let `X` be an algebraic stack. There exists a surjective
smooth scheme atlas with property `P` if and only if there exists a surjective
smooth algebraic-space atlas with property `P`. -/
@[stacks 04YF]
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmooth_iff_existsSurjectiveSmoothSpace :
  ∀ {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (X : GroupoidsOver S) [AlgebraicStack X],
    existsSurjectiveSmooth P X ↔ existsSurjectiveSmoothSpace P X)

/- Lemma 100.7.1 (3): let `P` be a property of schemes which is local in the
smooth topology, and let `X` be an algebraic stack. There exists an algebraic
space `U` and a surjective smooth morphism `U ⟶ X` such that `U` has property
`P` if and only if every smooth morphism `U ⟶ X` from an algebraic space has
property `P` on the source. -/
@[stacks 04YF]
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmoothSpace_iff_forallSmoothSpace :
  ∀ {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (X : GroupoidsOver S) [AlgebraicStack X],
    existsSurjectiveSmoothSpace P X ↔ forallSmoothSpace P X)

/- Lemma 100.7.1 (4): if `X` is a scheme `U` over `S`, then
`existsSurjectiveSmooth P (GroupoidsOver.slice U)` is equivalent to `P U.left`. -/
@[stacks 04YF]
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmooth_slice :
  ∀ {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (U : Over S),
    existsSurjectiveSmooth P (GroupoidsOver.slice U) ↔ P U.left)

/- Lemma 100.7.1 (5): if `X` is an algebraic space `F` over `S`, then
`existsSurjectiveSmooth P F.toGroupoids` is equivalent to `F` having property
`P`. -/
@[stacks 04YF]
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmooth_toGroupoids :
  ∀ {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (F : AlgebraicSpace S),
    existsSurjectiveSmooth P F.toGroupoids ↔
      AlgebraicSpace.existsSurjectiveEtale P F)

/- If `U` is a scheme over `S`, then every smooth morphism from a scheme to
`GroupoidsOver.slice U` has property `P` if and only if `U.left` has property
`P`. -/
#check (AlgebraicGeometry.AlgebraicStack.forallSmooth_slice :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.bigSmoothPrecoverage] (U : Over S),
    forallSmooth P (GroupoidsOver.slice U) ↔ P U.left)

/- The smooth-local atlas criterion transports along an equivalence to a
scheme slice. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmooth_equivalence :
  ∀ {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (e : X ≌ GroupoidsOver.slice U),
    existsSurjectiveSmooth P X ↔ P U.left)

/- If `P` is also étale-local, the algebraic-space specialization of
`existsSurjectiveSmooth` is `AlgebraicSpace.hasEtaleLocal`. -/
#check (AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmooth_hasEtaleLocal :
  ∀ {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    [P.IsLocal Scheme.etalePrecoverage] (F : AlgebraicSpace S),
    existsSurjectiveSmooth P F.toGroupoids ↔
      AlgebraicSpace.hasEtaleLocal P F)

end AlgebraicGeometry.AlgebraicStack
