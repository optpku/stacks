module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Irreducible
public import stacks_project.Chap107.Definition_107_4_1_VersalRing

/-!
# Formal branches of an algebraic stack through a finite type point

The formal branches of an algebraic stack `X` through a finite type field-valued
point `x0` are the irreducible components of `Spec(ξ.base)` for any versal
formal object `ξ` of `X` at `x0`, identified across choices of `ξ` by the
homotopy-unique power-series object comparison of minimal primes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing TopologicalSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- A morphism of complete local `S`-algebras is a power-series extension when
the target is isomorphic to a finite-variable power series ring over the
source, identifying the underlying ring map with the canonical coefficient
inclusion. Source maps `φ : A → A'` are `CompleteLocalSAlgebra.Hom A' A`. -/
def IsPowerSeriesExtension {A A' : CompleteLocalSAlgebra S}
    (φ : CompleteLocalSAlgebra.Hom A' A) : Prop :=
  ∃ n : ℕ, ∃ e : A'.carrier ≃+* MvPowerSeries (Fin n) A.carrier,
    e.toRingHom.comp φ.hom = MvPowerSeries.C

/-- A power-series extension is a ring isomorphism to a finite-variable power
series ring carrying the underlying local map to the coefficient inclusion. -/
theorem isPowerSeriesExtension_iff {A A' : CompleteLocalSAlgebra S}
    (φ : CompleteLocalSAlgebra.Hom A' A) :
    IsPowerSeriesExtension φ ↔
      ∃ n : ℕ, ∃ e : A'.carrier ≃+* MvPowerSeries (Fin n) A.carrier,
        e.toRingHom.comp φ.hom = MvPowerSeries.C := sorry

/-- A morphism of complete local `S`-algebras extends the minimal prime of an
irreducible component of `Spec(A)` to that of an irreducible component of
`Spec(A')` when the image of the corresponding minimal prime is the
corresponding minimal prime. -/
def ExtendsMinimalPrime {A A' : CompleteLocalSAlgebra S}
    (φ : CompleteLocalSAlgebra.Hom A' A)
    (Z : irreducibleComponents (PrimeSpectrum A.carrier))
    (W : irreducibleComponents (PrimeSpectrum A'.carrier)) : Prop :=
  ∃ p : PrimeSpectrum A.carrier,
    p.asIdeal ∈ minimalPrimes A.carrier ∧
      closure ({p} : Set (PrimeSpectrum A.carrier)) = (Z : Set _) ∧
        ∃ q : PrimeSpectrum A'.carrier,
          q.asIdeal = Ideal.map φ.hom p.asIdeal ∧
            q.asIdeal ∈ minimalPrimes A'.carrier ∧
              closure ({q} : Set (PrimeSpectrum A'.carrier)) = (W : Set _)

/-- Extending a minimal prime unpacks to a pair of minimal primes, one the
image of the other, whose closures are the given irreducible components. -/
theorem extendsMinimalPrime_iff {A A' : CompleteLocalSAlgebra S}
    (φ : CompleteLocalSAlgebra.Hom A' A)
    (Z : irreducibleComponents (PrimeSpectrum A.carrier))
    (W : irreducibleComponents (PrimeSpectrum A'.carrier)) :
    ExtendsMinimalPrime φ Z W ↔
      ∃ p : PrimeSpectrum A.carrier,
        p.asIdeal ∈ minimalPrimes A.carrier ∧
          closure ({p} : Set (PrimeSpectrum A.carrier)) = (Z : Set _) ∧
            ∃ q : PrimeSpectrum A'.carrier,
              q.asIdeal = Ideal.map φ.hom p.asIdeal ∧
                q.asIdeal ∈ minimalPrimes A'.carrier ∧
                  closure ({q} : Set (PrimeSpectrum A'.carrier)) =
                    (W : Set _) := sorry

/-- Morphisms of complete local `S`-algebras are formally homotopic when they
factor through a common power-series cylinder in the sense of formal homotopy. -/
def FormallyHomotopic {A B : CompleteLocalSAlgebra S}
    (φ ψ : CompleteLocalSAlgebra.Hom B A) : Prop :=
  ∃ (r : ℕ) (h : A.carrier →+* MvPowerSeries (Fin r) A.carrier)
    (k : MvPowerSeries (Fin r) A.carrier →+* B.carrier),
    k.comp MvPowerSeries.C = φ.hom ∧
      k.comp h = ψ.hom ∧
        MvPowerSeries.constantCoeff.comp h = RingHom.id A.carrier

/-- Formal homotopy unpacks to a cylinder factorization through a finite-variable
power series ring. -/
theorem formallyHomotopic_iff {A B : CompleteLocalSAlgebra S}
    (φ ψ : CompleteLocalSAlgebra.Hom B A) :
    FormallyHomotopic φ ψ ↔
      ∃ (r : ℕ) (h : A.carrier →+* MvPowerSeries (Fin r) A.carrier)
        (k : MvPowerSeries (Fin r) A.carrier →+* B.carrier),
        k.comp MvPowerSeries.C = φ.hom ∧
          k.comp h = ψ.hom ∧
            MvPowerSeries.constantCoeff.comp h = RingHom.id A.carrier := sorry

/-- Formally homotopic maps extend a given minimal prime to the same ideal. -/
theorem FormallyHomotopic.extendsMinimalPrime_eq {A B : CompleteLocalSAlgebra S}
    {φ ψ : CompleteLocalSAlgebra.Hom B A} (h : FormallyHomotopic φ ψ)
    {Z : irreducibleComponents (PrimeSpectrum A.carrier)}
    {W W' : irreducibleComponents (PrimeSpectrum B.carrier)} :
    ExtendsMinimalPrime φ Z W → ExtendsMinimalPrime ψ Z W' → W = W' := sorry


variable {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]

/-- A power-series morphism of complete local `S`-algebras is an object
comparison from `ξ` to `η` when it is the base of a morphism of formal
objects exhibiting `η` as the pushforward of this `ξ`. -/
def IsObjectComparison (ξ η : GroupoidsOver.FormalObject X)
    (φ : CompleteLocalSAlgebra.Hom η.base ξ.base) : Prop :=
  IsPowerSeriesExtension φ ∧
    ∃ f : GroupoidsOver.FormalObject.Hom η ξ, f.base.hom = φ.hom

/-- An object comparison is a power-series extension that is the base of a
morphism of formal objects from the pushforward to the original object. -/
theorem isObjectComparison_iff (ξ η : GroupoidsOver.FormalObject X)
    (φ : CompleteLocalSAlgebra.Hom η.base ξ.base) :
    IsObjectComparison ξ η φ ↔
      IsPowerSeriesExtension φ ∧
        ∃ f : GroupoidsOver.FormalObject.Hom η ξ, f.base.hom = φ.hom := sorry

/-- Irreducible components of the spectra of two formal objects are identified
when an object comparison in one direction or the other carries one minimal
prime onto the other. -/
def Identified (ξ η : GroupoidsOver.FormalObject X)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier))
    (W : irreducibleComponents (PrimeSpectrum η.base.carrier)) : Prop :=
  (∃ φ : CompleteLocalSAlgebra.Hom η.base ξ.base,
      IsObjectComparison ξ η φ ∧ ExtendsMinimalPrime φ Z W) ∨
    ∃ φ : CompleteLocalSAlgebra.Hom ξ.base η.base,
      IsObjectComparison η ξ φ ∧ ExtendsMinimalPrime φ W Z

/-- Identification of components is an object comparison in one direction or
the other carrying one minimal prime onto the other. -/
theorem identified_iff (ξ η : GroupoidsOver.FormalObject X)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier))
    (W : irreducibleComponents (PrimeSpectrum η.base.carrier)) :
    Identified ξ η Z W ↔
      (∃ φ : CompleteLocalSAlgebra.Hom η.base ξ.base,
          IsObjectComparison ξ η φ ∧ ExtendsMinimalPrime φ Z W) ∨
        ∃ φ : CompleteLocalSAlgebra.Hom ξ.base η.base,
          IsObjectComparison η ξ φ ∧ ExtendsMinimalPrime φ W Z := sorry

/-- Identification of irreducible components is reflexive. -/
theorem Identified.refl (ξ : GroupoidsOver.FormalObject X)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) :
    Identified ξ ξ Z Z := sorry

/-- Identification of irreducible components is symmetric. -/
theorem Identified.symm {ξ η : GroupoidsOver.FormalObject X}
    {Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)}
    {W : irreducibleComponents (PrimeSpectrum η.base.carrier)} :
    Identified ξ η Z W → Identified η ξ W Z := sorry

/-- Identification of irreducible components is transitive. -/
theorem Identified.trans {ξ η ζ : GroupoidsOver.FormalObject X}
    {Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)}
    {W : irreducibleComponents (PrimeSpectrum η.base.carrier)}
    {Y : irreducibleComponents (PrimeSpectrum ζ.base.carrier)} :
    Identified ξ η Z W → Identified η ζ W Y → Identified ξ ζ Z Y := sorry

variable (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]

/-- Any two object comparisons of a fixed ordered pair of versal formal objects
at `x0` are formally homotopic. -/
theorem isObjectComparison_formallyHomotopic
    {ξ η : GroupoidsOver.FormalObject X}
    [GroupoidsOver.FormalObject.IsVersal ξ]
    [GroupoidsOver.FormalObject.IsVersal η]
    (hξ : StageOneCompatible x0 ξ) (hη : StageOneCompatible x0 η)
    {φ ψ : CompleteLocalSAlgebra.Hom η.base ξ.base}
    (hφ : IsObjectComparison ξ η φ) (hψ : IsObjectComparison ξ η ψ) :
    FormallyHomotopic φ ψ := sorry

/-- On a single versal formal object at `x0`, identified components are equal. -/
theorem identified_self_iff (ξ : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ] (hξ : StageOneCompatible x0 ξ)
    (Z W : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) :
    Identified ξ ξ Z W ↔ Z = W := sorry

/-- The set of formal branches of `X` through `x0`, as identified irreducible
components of `Spec(ξ.base)` for versal formal objects `ξ` of `X` at `x0`. -/
def FormalBranches : Type (u + 1) :=
  Quot fun (r r' :
      (ξ : GroupoidsOver.FormalObject X) ×
        PSigma fun _ : GroupoidsOver.FormalObject.IsVersal ξ =>
          PSigma fun _ : StageOneCompatible x0 ξ =>
            irreducibleComponents (PrimeSpectrum ξ.base.carrier)) =>
    Identified r.1 r'.1 r.2.2.2 r'.2.2.2

namespace FormalBranches

/-- The formal branch represented by an irreducible component of `Spec(ξ.base)`
for a versal formal object `ξ` of `X` at `x0`. -/
def mk (ξ : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ] (hξ : StageOneCompatible x0 ξ)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) :
    FormalBranches x0 :=
  Quot.mk _ ⟨ξ, ⟨inferInstance, ⟨hξ, Z⟩⟩⟩

/-- Components of two versal formal objects at `x0` determine the same formal
branch if and only if they are identified by an object comparison of minimal
primes. -/
theorem mk_eq_mk_iff {ξ η : GroupoidsOver.FormalObject X}
    [GroupoidsOver.FormalObject.IsVersal ξ]
    [GroupoidsOver.FormalObject.IsVersal η]
    (hξ : StageOneCompatible x0 ξ) (hη : StageOneCompatible x0 η)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier))
    (W : irreducibleComponents (PrimeSpectrum η.base.carrier)) :
    mk x0 ξ hξ Z = mk x0 η hη W ↔ Identified ξ η Z W := sorry

/-- For any versal formal object `ξ` of `X` at `x0`, every formal branch arises
uniquely from an irreducible component of `Spec(ξ.base)`. -/
theorem spec (ξ : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ] (hξ : StageOneCompatible x0 ξ) :
    Function.Surjective (mk x0 ξ hξ) ∧
      ∀ Z W, mk x0 ξ hξ Z = mk x0 ξ hξ W ↔ Z = W := sorry

/-- Irreducible components of the prime spectrum of a complete local
`S`-algebra correspond to irreducible components of the affine scheme
`Spec(A)`. -/
theorem components_spec (A : CompleteLocalSAlgebra S) :
    Nonempty
      (irreducibleComponents (PrimeSpectrum A.carrier) ≃
        irreducibleComponents (Spec (CommRingCat.of A.carrier))) := sorry

end FormalBranches

end AlgebraicGeometry.AlgebraicStack
