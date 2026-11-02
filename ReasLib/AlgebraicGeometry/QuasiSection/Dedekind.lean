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
public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
public import Mathlib.NumberTheory.ClassNumber.Finite
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.PicardGroup
public import ReasLib.AlgebraicGeometry.QuasiSection.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.FieldTheory.PrimeField.PowerCriterion
public import ReasLib.RingTheory.Excellent.Dedekind
public import ReasLib.RingTheory.Excellent.EssentialFiniteness

@[expose] public section

universe u v

open CategoryTheory CommRingCat

noncomputable section

namespace AlgebraicGeometry

private theorem isPrimeAlgebraic_of_finite (K : Type*) [Field K] [Finite K] :
    FieldExtension.IsPrimeAlgebraic K := by
  let p := ringChar K
  let hchar : CharP K p := ringChar.charP K
  have hp : p.Prime := CharP.char_is_prime K p
  letI : Fact p.Prime := ⟨hp⟩
  letI : Algebra (ZMod p) K := @ZMod.algebra K _ p hchar
  exact ⟨p, hp, hchar, Algebra.IsAlgebraic.of_finite (ZMod p) K⟩

/-- Residue fields of `A` at maximal ideals are algebraic over a finite field. -/
class ResidueFieldsPrimeAlgebraic (A : Type u) [CommRing A] : Prop where
  /-- Every maximal residue field is algebraic over its prime field. -/
  isPrimeAlgebraic_residueField :
    ∀ (m : Ideal A) [m.IsMaximal], FieldExtension.IsPrimeAlgebraic m.ResidueField

/-- The residue-field hypothesis is the pointwise prime-field algebraicity condition. -/
theorem residueFieldsPrimeAlgebraic_iff {A : Type u} [CommRing A] :
    ResidueFieldsPrimeAlgebraic A ↔
      ∀ (m : Ideal A) [m.IsMaximal], FieldExtension.IsPrimeAlgebraic m.ResidueField := by
  constructor
  · intro h m hm
    exact h.isPrimeAlgebraic_residueField m
  · intro h
    exact ⟨fun m _ ↦ h m⟩

/-- Residue fields of `ℤ` at maximal ideals are finite, hence prime-field algebraic. -/
instance instResidueFieldsPrimeAlgebraic_int : ResidueFieldsPrimeAlgebraic ℤ := by
  constructor
  intro m hm
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm Int.not_isField
  haveI : Finite (ℤ ⧸ m) := Ring.HasFiniteQuotients.finiteQuotient hm0
  exact isPrimeAlgebraic_of_finite m.ResidueField

/-- Residue fields of `Polynomial (ZMod p)` at maximal ideals are finite extensions of
`ZMod p`. -/
instance instResidueFieldsPrimeAlgebraic_polynomialZMod (p : ℕ) [Fact p.Prime] :
    ResidueFieldsPrimeAlgebraic (Polynomial (ZMod p)) := by
  constructor
  intro m hm
  haveI : Algebra.FiniteType (ZMod p) m.ResidueField :=
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType (ZMod p) (Polynomial (ZMod p)))
      (inferInstance : Algebra.FiniteType (Polynomial (ZMod p)) m.ResidueField)
  haveI : Module.Finite (ZMod p) m.ResidueField :=
    finite_of_finite_type_of_isJacobsonRing _ _
  haveI : Finite m.ResidueField := Module.finite_of_finite (ZMod p)
  exact isPrimeAlgebraic_of_finite m.ResidueField

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
        Monoid.IsTorsion (CommRing.Pic (integralClosure A L)) := by
  constructor
  · intro h L _ _ _ _ _
    exact h.pic_torsion L
  · intro h
    exact ⟨fun L _ _ _ _ _ ↦ h L⟩

private theorem picTorsion_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : Monoid.IsTorsion (CommRing.Pic R)) :
    Monoid.IsTorsion (CommRing.Pic S) := by
  apply IsTorsion.of_surjective (f := CommRing.Pic.mapRingHom e.toRingHom) ?_ h
  intro M
  refine ⟨CommRing.Pic.mapRingHom e.symm.toRingHom M, ?_⟩
  rw [CommRing.Pic.mapRingHom_mapRingHom]
  simpa using CommRing.Pic.mapRingHom_id_apply (M := M)

/-- Transport the finite-extension condition to an arbitrary universe. -/
private theorem picTorsion_integralClosure {R : Type v} [CommRing R] [IsDomain R]
    [FiniteIntegralClosurePicTorsion R] (L : Type u) [Field L]
    [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L] :
    Monoid.IsTorsion (CommRing.Pic (integralClosure R L)) := by
  letI : Small.{v} L := Module.Finite.small (FractionRing R) L
  letI : IsScalarTower R (FractionRing R) (Shrink.{v} L) :=
    LinearEquiv.isScalarTower (FractionRing R) (Shrink.linearEquiv R L)
  have h := FiniteIntegralClosurePicTorsion.pic_torsion (A := R) (Shrink.{v} L)
  exact picTorsion_of_ringEquiv ((Shrink.algEquiv R L).mapIntegralClosure).toRingEquiv h

/-- A finite injective extension preserves the integral-closure Picard-torsion condition. -/
private theorem finiteIntegralClosurePicTorsion_of_moduleFinite
    (R : Type v) [CommRing R] [IsDomain R] [FiniteIntegralClosurePicTorsion R]
    (A : Type u) [CommRing A] [IsDomain A]
    [Algebra R A] [Module.Finite R A] (hinj : Function.Injective (algebraMap R A)) :
    FiniteIntegralClosurePicTorsion A := by
  constructor
  intro L _ _ _ _ _
  letI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hinj
  letI : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra R _
  letI := FractionRing.isScalarTower_liftAlgebra R (FractionRing A)
  haveI : FiniteDimensional (FractionRing R) (FractionRing A) := inferInstance
  letI : Algebra (FractionRing R) L :=
    ((algebraMap (FractionRing A) L).comp
      (algebraMap (FractionRing R) (FractionRing A))).toAlgebra
  letI : Algebra R L := ((algebraMap A L).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (FractionRing R) (FractionRing A) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R (FractionRing A) L :=
    IsScalarTower.to₁₃₄ R A (FractionRing A) L
  letI : IsScalarTower R (FractionRing R) L :=
    IsScalarTower.to₁₂₄ R (FractionRing R) (FractionRing A) L
  haveI : FiniteDimensional (FractionRing R) L :=
    Module.Finite.trans (FractionRing A) L
  haveI : IsIntegralClosure (integralClosure A L) R L := by
    constructor
    · exact Subtype.coe_injective
    · intro x
      constructor
      · intro hx
        exact ⟨⟨x, hx.tower_top⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact isIntegral_trans (R := R) _ y.property
  exact picTorsion_of_ringEquiv
    (IsIntegralClosure.equiv R (integralClosure R L) L (integralClosure A L)).toRingEquiv
    (picTorsion_integralClosure L)

/-- Finite integral closures of `ℤ` have finite class groups, hence torsion Picard groups. -/
instance instFiniteIntegralClosurePicTorsion_int : FiniteIntegralClosurePicTorsion ℤ := by
  constructor
  intro L _ _ _ _ _
  letI : Fintype (ClassGroup (integralClosure ℤ L)) :=
    ClassGroup.fintypeOfAdmissibleOfFinite (FractionRing ℤ) L AbsoluteValue.absIsAdmissible
  haveI : Finite (CommRing.Pic (integralClosure ℤ L)) :=
    Finite.of_equiv (ClassGroup (integralClosure ℤ L)) (ClassGroup.equivPic _).toEquiv
  exact isTorsion_of_finite

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
    HasQuasiSection f := by
  haveI : ResidueFieldsPrimeAlgebraic A := by
    constructor
    intro m hm
    haveI : Finite (A ⧸ m) :=
      Ring.HasFiniteQuotients.finiteQuotient (Ideal.IsMaximal.ne_bot_of_isIntegral_int m)
    exact isPrimeAlgebraic_of_finite m.ResidueField
  haveI : FiniteIntegralClosurePicTorsion A :=
    finiteIntegralClosurePicTorsion_of_moduleFinite ℤ A
      (FaithfulSMul.algebraMap_injective ℤ A)
  exact hasQuasiSection_of_dedekind f

/-- A finite Dedekind extension of a finite-prime-field polynomial ring satisfies the arithmetic
quasi-section criterion when its coefficient algebra map is injective. -/
theorem hasQuasiSection_of_finite_polynomialZMod (p : ℕ) [Fact p.Prime]
    {A : Type u} [CommRing A] [IsDedekindDomain A]
    [Algebra (Polynomial (ZMod p)) A] [Module.Finite (Polynomial (ZMod p)) A]
    (h_injective : Function.Injective (algebraMap (Polynomial (ZMod p)) A))
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [Surjective f]
    [Scheme.Hom.FiniteType f]
    [GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec (.of A))))] :
    HasQuasiSection f := by
  letI : IsExcellentRing.{u, u} A :=
    IsExcellentRing.of_finiteType (Polynomial (ZMod p))
  haveI : FiniteIntegralClosurePicTorsion A :=
    finiteIntegralClosurePicTorsion_of_moduleFinite (Polynomial (ZMod p)) A h_injective
  letI : Algebra (ZMod p) A :=
    ((algebraMap (Polynomial (ZMod p)) A).comp Polynomial.C).toAlgebra
  letI : IsScalarTower (ZMod p) (Polynomial (ZMod p)) A :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType (ZMod p) A :=
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType (ZMod p) (Polynomial (ZMod p)))
      (inferInstance : Algebra.FiniteType (Polynomial (ZMod p)) A)
  haveI : ResidueFieldsPrimeAlgebraic A := by
    constructor
    intro m hm
    haveI : Algebra.FiniteType (ZMod p) m.ResidueField :=
      Algebra.FiniteType.trans
        (inferInstance : Algebra.FiniteType (ZMod p) A)
        (inferInstance : Algebra.FiniteType A m.ResidueField)
    haveI : Module.Finite (ZMod p) m.ResidueField :=
      finite_of_finite_type_of_isJacobsonRing _ _
    haveI : Finite m.ResidueField := Module.finite_of_finite (ZMod p)
    exact isPrimeAlgebraic_of_finite m.ResidueField
  exact hasQuasiSection_of_dedekind f

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
