/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.QuasiSection.Morphism
public import ReasLib.AlgebraicGeometry.QuasiSection.Dedekind
public import ReasLib.AlgebraicGeometry.QuasiSection.Examples
public import ReasLib.AlgebraicGeometry.QuasiSection.Counterexample
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CommRingCat

noncomputable section

namespace AlgebraicGeometry

/- Remark 111.34.9 (1): Exercise 111.34.7 produces a finite surjective morphism
`GoldenIntegerQuasiSection.scheme ⟶ Spec (of ℤ)` over the localized affine line,
so `GoldenIntegerQuasiSection.ambientToSpecInt` has a quasi-section. -/
@[stacks 02F2] #check
  (AlgebraicGeometry.GoldenIntegerQuasiSection.hasQuasiSection_ambientToSpecInt :
    HasQuasiSection GoldenIntegerQuasiSection.ambientToSpecInt)

/- Remark 111.34.9 (2): Exercise 111.34.8 produces a finite surjective closed
subscheme of `FpTAwayAffineLine.total p` over `Spec (Polynomial (ZMod p))`, so
`FpTAwayAffineLine.toBase p` has a quasi-section. -/
@[stacks 02F2] #check
  (AlgebraicGeometry.FpTAwayAffineLine.hasQuasiSection_toBase :
    ∀ (p : ℕ) [Fact p.Prime], HasQuasiSection (FpTAwayAffineLine.toBase p))

/- Remark 111.34.9 (3): if `A` is an excellent Dedekind domain whose residue
fields at maximal ideals are algebraic over finite fields and whose finite
integral closures have torsion Picard groups, then every flat surjective morphism
of finite type to `Spec (of A)` with geometrically irreducible generic fibre has
a quasi-section. -/
@[stacks 02F2] #check
  (AlgebraicGeometry.hasQuasiSection_of_dedekind :
    ∀ {A : Type u} [CommRing A] [IsDedekindDomain A] [IsExcellentRing.{u, u} A]
      [ResidueFieldsPrimeAlgebraic A] [FiniteIntegralClosurePicTorsion A]
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [Surjective f]
      [Scheme.Hom.FiniteType f]
      [GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec (.of A))))],
      HasQuasiSection f)

/- The criterion specializes to finite Dedekind extensions of the two basic arithmetic rings. -/
#check
  (AlgebraicGeometry.hasQuasiSection_of_finite_int :
    ∀ {A : Type u} [CommRing A] [IsDedekindDomain A] [CharZero A] [Module.Finite ℤ A]
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [Surjective f]
      [Scheme.Hom.FiniteType f]
      [GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec (.of A))))],
      HasQuasiSection f)

#check
  (AlgebraicGeometry.hasQuasiSection_of_finite_polynomialZMod :
    ∀ (p : ℕ) [Fact p.Prime] {A : Type u} [CommRing A] [IsDedekindDomain A]
      [Algebra (Polynomial (ZMod p)) A] [Module.Finite (Polynomial (ZMod p)) A]
      (h_injective : Function.Injective (algebraMap (Polynomial (ZMod p)) A))
      {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [Surjective f]
      [Scheme.Hom.FiniteType f]
      [GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec (.of A))))],
      HasQuasiSection f)

/- Remark 111.34.9 (4): Goldman constructed a Dedekind domain with finite residue
fields at maximal ideals whose Picard group is not torsion. -/
@[stacks 02F2] #check
  (AlgebraicGeometry.exists_dedekind_finiteResidue_not_picTorsion :
    ∃ (A : Type u) (_ : CommRing A),
      IsDedekindDomain A ∧
        (∀ (m : Ideal A) [m.IsMaximal], Finite m.ResidueField) ∧
        ¬ Monoid.IsTorsion (CommRing.Pic A))

/- Remark 111.34.9 (5): the quasi-section existence theorem fails for the
spectrum of a Goldman Dedekind domain: some flat surjective morphism of finite
type with geometrically irreducible generic fibre has no quasi-section. -/
@[stacks 02F2] #check
  (AlgebraicGeometry.exists_dedekind_not_hasQuasiSection :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDedekindDomain A),
      (∀ (m : Ideal A) [m.IsMaximal], Finite m.ResidueField) ∧
        ¬ Monoid.IsTorsion (CommRing.Pic A) ∧
        ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)),
          Flat f ∧ Surjective f ∧ Scheme.Hom.FiniteType f ∧
            GeometricallyIrreducible
              (f.fiberToSpecResidueField (genericPoint (Spec (.of A)))) ∧
            ¬ HasQuasiSection f)

/- Remark 111.34.9 (6): Exercise 111.34.10 is a geometric example over
`Polynomial ℂ` where a quasi-section fails. -/
@[stacks 02F2] #check
  (AlgebraicGeometry.NoQuasiSection.exists_polynomial :
    ∃ f : NoQuasiSection.PlaneRing, (∀ α : ℂ, ¬ NoQuasiSection.linearFactor α ∣ f) ∧
      ¬ NoQuasiSection.HasFiniteSurjectiveClosedSubscheme f)

end AlgebraicGeometry
