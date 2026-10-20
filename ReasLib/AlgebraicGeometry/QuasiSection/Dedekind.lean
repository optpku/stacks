/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Data.Finite.Defs
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.PicardGroup
public import ReasLib.AlgebraicGeometry.QuasiSection.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.FieldTheory.PrimeField.PowerCriterion
public import ReasLib.RingTheory.Excellent.Dedekind

@[expose] public section

universe u

open CategoryTheory CommRingCat

noncomputable section

namespace AlgebraicGeometry

/-- Residue fields of `A` at maximal ideals are algebraic over a finite field. -/
class ResidueFieldsPrimeAlgebraic (A : Type u) [CommRing A] : Prop where
  /-- Every maximal residue field is algebraic over its prime field. -/
  isPrimeAlgebraic_residueField :
    ∀ (m : Ideal A) [m.IsMaximal], FieldExtension.IsPrimeAlgebraic m.ResidueField

/-- The residue-field hypothesis is the pointwise prime-field algebraicity condition. -/
theorem residueFieldsPrimeAlgebraic_iff {A : Type u} [CommRing A] :
    ResidueFieldsPrimeAlgebraic A ↔
      ∀ (m : Ideal A) [m.IsMaximal], FieldExtension.IsPrimeAlgebraic m.ResidueField := sorry

/-- Residue fields of `ℤ` at maximal ideals are finite, hence prime-field algebraic. -/
instance instResidueFieldsPrimeAlgebraic_int : ResidueFieldsPrimeAlgebraic ℤ := sorry

/-- Residue fields of `Polynomial (ZMod p)` at maximal ideals are finite extensions of
`ZMod p`. -/
instance instResidueFieldsPrimeAlgebraic_polynomialZMod (p : ℕ) [Fact p.Prime] :
    ResidueFieldsPrimeAlgebraic (Polynomial (ZMod p)) := sorry

/-- Picard groups of finite integral closures of `A` are torsion groups. -/
class FiniteIntegralClosurePicTorsion (A : Type u) [CommRing A] [IsDomain A] : Prop where
  /-- If `L` is a finite extension of `FractionRing A`, then
  `CommRing.Pic (integralClosure A L)` is torsion. -/
  pic_torsion :
    ∀ (L : Type u) [Field L] [Algebra A L] [Algebra (FractionRing A) L]
      [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L],
      Monoid.IsTorsion (CommRing.Pic (integralClosure A L))

/-- The Picard-torsion hypothesis is the condition on finite integral closures. -/
theorem finiteIntegralClosurePicTorsion_iff {A : Type u} [CommRing A] [IsDomain A] :
    FiniteIntegralClosurePicTorsion A ↔
      ∀ (L : Type u) [Field L] [Algebra A L] [Algebra (FractionRing A) L]
        [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L],
        Monoid.IsTorsion (CommRing.Pic (integralClosure A L)) := sorry

/-- Finite integral closures of `ℤ` have finite class groups, hence torsion Picard groups. -/
instance instFiniteIntegralClosurePicTorsion_int : FiniteIntegralClosurePicTorsion ℤ := sorry

/-- Finite integral closures of `Polynomial (ZMod p)` have torsion Picard groups. -/
instance instFiniteIntegralClosurePicTorsion_polynomialZMod (p : ℕ) [Fact p.Prime] :
    FiniteIntegralClosurePicTorsion (Polynomial (ZMod p)) := sorry

/-- A flat surjective morphism of finite type to the spectrum of an excellent Dedekind
domain has a quasi-section if its generic fibre is geometrically irreducible, its maximal
residue fields are algebraic over finite fields, and finite integral closures of the domain
have torsion Picard groups. -/
theorem hasQuasiSection_of_dedekind {A : Type u} [CommRing A] [IsDedekindDomain A]
    [IsExcellentRing.{u, u} A] [ResidueFieldsPrimeAlgebraic A]
    [FiniteIntegralClosurePicTorsion A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [Flat f] [Surjective f] [Scheme.Hom.FiniteType f]
    [GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec (.of A))))] :
    HasQuasiSection f := sorry

/-- A finite Dedekind extension of `ℤ` satisfies the arithmetic quasi-section criterion. -/
theorem hasQuasiSection_of_finite_int {A : Type u} [CommRing A] [IsDedekindDomain A]
    [CharZero A] [Module.Finite ℤ A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [Flat f] [Surjective f] [Scheme.Hom.FiniteType f]
    [GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec (.of A))))] :
    HasQuasiSection f := sorry

/-- A finite Dedekind extension of a finite-prime-field polynomial ring satisfies the arithmetic
quasi-section criterion when its coefficient algebra map is injective. -/
theorem hasQuasiSection_of_finite_polynomialZMod (p : ℕ) [Fact p.Prime]
    {A : Type u} [CommRing A] [IsDedekindDomain A]
    [Algebra (Polynomial (ZMod p)) A] [Module.Finite (Polynomial (ZMod p)) A]
    (h_injective : Function.Injective (algebraMap (Polynomial (ZMod p)) A))
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [Surjective f]
    [Scheme.Hom.FiniteType f]
    [GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec (.of A))))] :
    HasQuasiSection f := sorry

/-- There is a Dedekind domain with finite residue fields at maximal ideals whose Picard
group is not torsion. -/
theorem exists_dedekind_finiteResidue_not_picTorsion :
    ∃ (A : Type u) (_ : CommRing A),
      IsDedekindDomain A ∧
        (∀ (m : Ideal A) [m.IsMaximal], Finite m.ResidueField) ∧
        ¬ Monoid.IsTorsion (CommRing.Pic A) := sorry

/-- Over some Dedekind domain with finite maximal residue fields and nontorsion Picard
group, a flat surjective morphism of finite type with geometrically irreducible generic
fibre has no quasi-section. -/
theorem exists_dedekind_not_hasQuasiSection :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDedekindDomain A),
      (∀ (m : Ideal A) [m.IsMaximal], Finite m.ResidueField) ∧
        ¬ Monoid.IsTorsion (CommRing.Pic A) ∧
        ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)),
          Flat f ∧ Surjective f ∧ Scheme.Hom.FiniteType f ∧
            GeometricallyIrreducible
              (f.fiberToSpecResidueField (genericPoint (Spec (.of A)))) ∧
            ¬ HasQuasiSection f := sorry

end AlgebraicGeometry
