/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Length
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Localization.FractionRing.Separable
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.RegularLocalRing.Domain

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- The length over an affine base of the first cohomology of the structure sheaf. -/
noncomputable abbrev structureSheafH1Length
    (f : X ⟶ Spec (.of A)) : ℕ∞ :=
  Module.length A
    (cohomology f (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1)

/-- `structureSheafH1Length` is the module length of affine-base structure-sheaf cohomology. -/
theorem structureSheafH1Length_def (f : X ⟶ Spec (.of A)) :
    structureSheafH1Length f =
      Module.length A
        (cohomology f (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1) := sorry

end AlgebraicGeometry.Scheme.Hom

namespace RationalSingularity

/-- Reduction to rational singularities is possible when the first structure-sheaf cohomology
of every normal modification has uniformly bounded finite length. -/
class ReductionPossible (A : Type u) [CommRing A] : Prop where
  /-- The base ring is local. -/
  isLocalRing : IsLocalRing A
  /-- The base ring is Nagata. -/
  nagataRing : NagataRing A
  /-- The base ring is normal. -/
  isNormalRing : IsNormalRing A
  /-- The base ring has Krull dimension two. -/
  dimension_eq : ringKrullDim A = 2
  /-- The lengths of `H¹(X, 𝒪_X)` are bounded over all normal modifications of `Spec A`. -/
  h1Length_bounded : ∃ n : ℕ, ∀ (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [IsModification f], X.isNormal →
      Scheme.Hom.structureSheafH1Length f ≤ (n : ℕ∞)

namespace ReductionPossible

/-- A ring for which reduction to rational singularities is possible is local. -/
instance instIsLocalRing (A : Type u) [CommRing A] [ReductionPossible A] :
    IsLocalRing A := sorry

/-- A ring for which reduction to rational singularities is possible is Nagata. -/
instance instNagataRing (A : Type u) [CommRing A] [ReductionPossible A] :
    NagataRing A := sorry

/-- A ring for which reduction to rational singularities is possible is normal. -/
instance instIsNormalRing (A : Type u) [CommRing A] [ReductionPossible A] :
    IsNormalRing A := sorry

/-- A finite injective local map between two-dimensional local normal Nagata domains
with separable induced fraction-field extension transfers reduction to rational singularities
from the source ring to the target ring. -/
theorem ascend
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [NagataRing B] [_root_.IsNormalRing B]
    [ReductionPossible A]
    (h_injective : Function.Injective (algebraMap A B))
    (h_dimension_B : ringKrullDim B = 2)
    (h_separable : FractionRing.isSeparableOf h_injective) :
    ReductionPossible B := sorry

/-- For a complete regular local ring of dimension two in prime characteristic,
an inseparable degree-prime extension of its fraction field has integral closure
with reduction to rational singularities possible. -/
theorem ofIntegralClosureInseparableDegreePrime
    (p : ℕ) (hp : p.Prime)
    (A : Type u) [CommRing A] [IsCompleteLocalRing A] [IsRegularLocalRing A]
    [CharP A p] (h_dimension : ringKrullDim A = 2)
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] (h_degree : Module.finrank K L = p)
    (h_inseparable : ¬ Algebra.IsSeparable K L) :
    ReductionPossible (integralClosure A L) := sorry

end ReductionPossible

/-- The defining conditions for reduction to rational singularities to be possible. -/
theorem reductionPossible_iff (A : Type u) [CommRing A] :
    ReductionPossible A ↔
      IsLocalRing A ∧ NagataRing A ∧ IsNormalRing A ∧ ringKrullDim A = 2 ∧
        ∃ n : ℕ, ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsModification f],
          X.isNormal → Scheme.Hom.structureSheafH1Length f ≤ (n : ℕ∞) := sorry

end RationalSingularity
