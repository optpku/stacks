/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Smooth.Adic.Basic
public import stacks_project.Chap90.Definition_90_9_1_Smooth
public import stacks_project.Chap101.Lemma_101_33_6_SourceLocus
public import stacks_project.Chap107.Definition_107_4_1_VersalRing
public import stacks_project.Chap107.Lemma_107_2_3
public import stacks_project.Chap107.Situation_107_2_1_Instances
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smoothness of the structure morphism at a finite-type point

In Situation 107.2.1, for a finite-type field-valued point and a versal ring at
that point, membership in the smooth source locus of `X ⟶ S` is equivalent to
`m_A`-adic formal smoothness of `O_{S,s} → A` and to unobstructedness of the
predeformation category `F_{X, k, x0}`.
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

/-- Lemma 107.2.7: In Situation 107.2.1 let `x0 : Spec(k) ⟶ X` be a morphism
such that `Spec(k) ⟶ S` is of finite type with image `s`. Let `A` be a versal
ring to `X` at `x0`. The following are equivalent: `x0` is in the smooth locus
of `X ⟶ S` (Morphisms of Stacks, Lemma 101.33.6); `O_{S,s} → A` is formally
smooth in the `m_A`-adic topology via `Scheme.stalkClosedPointTo A.toS`; and
`F_{X, k, x0}` is unobstructed. -/
@[stacks 0DZS]
theorem mem_sourceLocus_tfae {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] (s : S)
    (hs : x0.structureHom (closedPoint x0.K) = s) :
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
              x0.fiberObj)] :=
  sorry

/-- The structure morphism of a versal ring `A` sends the closed point of `A` to
the image `s` of `Spec(k) ⟶ S`. -/
theorem toS_closedPoint_eq {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] (s : S)
    (hs : x0.structureHom (closedPoint x0.K) = s) :
    A.toS (closedPoint A.carrier) = s :=
  sorry

/-- A finite-type field-valued point lies in the smooth source locus of
`X ⟶ S` if and only if `O_{S,s} → A` is formally smooth in the `m_A`-adic
topology. -/
theorem mem_sourceLocus_iff_formallySmooth {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] (s : S)
    (hs : x0.structureHom (closedPoint x0.K) = s) :
    Points.mk x0 ∈
        (Smooth.sourceLocus (baseProjection.{u + 1, u, u + 1} X)).pointsSet ↔
      (Scheme.stalkClosedPointTo A.toS).hom.formally_smooth_for_adic
        (maximalIdeal A.carrier) :=
  sorry

/-- A finite-type field-valued point lies in the smooth source locus of
`X ⟶ S` if and only if the predeformation category `F_{X, k, x0}` is
unobstructed. -/
theorem mem_sourceLocus_iff_isUnobstructed {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] (s : S)
    (hs : x0.structureHom (closedPoint x0.K) = s) :
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
            x0.fiberObj) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
