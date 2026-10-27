/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Smooth.Adic.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth.SourceLocus
public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Fiber

/-!
# Smooth loci, versal rings, and unobstructed deformations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open AlgebraicGeometry.GroupoidsOver.Predeformation
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- For an algebraic stack locally of finite type over a locally Noetherian scheme,
a finite-type field-valued point belongs to the smooth source locus if and only if
the canonical base-stalk map to a versal ring is formally smooth in its maximal-ideal-adic
topology, or equivalently its predeformation category is unobstructed. -/
theorem mem_sourceLocus_tfae {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] :
    List.TFAE
      [Points.mk x0 ∈
          (Smooth.sourceLocus (baseProjection.{u + 1, u, u + 1} X)).pointsSet,
        (Scheme.stalkClosedPointTo A.toS).hom.formally_smooth_for_adic
          (maximalIdeal A.carrier),
        ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
          [Module.Finite Λ x0.K]
          (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
          [IsOpenImmersion openImmersion]
          (h_factor :
            Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
              x0.structureHom),
          Functor.IsUnobstructed
            (predeformationFunctor X openImmersion x0.structureHom h_factor
              x0.fiberObj)] := sorry

/-- A finite-type field-valued point of an algebraic stack locally of finite type
over a locally Noetherian scheme lies in the smooth source locus if and only if
the canonical base-stalk map to a versal ring is formally smooth in its
maximal-ideal-adic topology. -/
theorem mem_sourceLocus_iff_formallySmooth {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] :
    Points.mk x0 ∈
        (Smooth.sourceLocus (baseProjection.{u + 1, u, u + 1} X)).pointsSet ↔
      (Scheme.stalkClosedPointTo A.toS).hom.formally_smooth_for_adic
        (maximalIdeal A.carrier) := sorry

/-- A finite-type field-valued point of an algebraic stack locally of finite type
over a locally Noetherian scheme lies in the smooth source locus if and only if
its predeformation category is unobstructed, for every Noetherian affine-open
coefficient presentation. -/
theorem mem_sourceLocus_iff_isUnobstructed {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] :
    Points.mk x0 ∈
        (Smooth.sourceLocus (baseProjection.{u + 1, u, u + 1} X)).pointsSet ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
        [Module.Finite Λ x0.K]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
            x0.structureHom),
        Functor.IsUnobstructed
          (predeformationFunctor X openImmersion x0.structureHom h_factor
            x0.fiberObj) := sorry

end AlgebraicGeometry.AlgebraicStack
