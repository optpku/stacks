/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Irreducible
public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing.Existence
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

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
                    (W : Set _) := Iff.rfl

/-- Morphisms of complete local `S`-algebras are formally homotopic when they
factor through a common power-series cylinder in the sense of formal homotopy. -/
def FormallyHomotopic {A B : CompleteLocalSAlgebra S}
    (φ ψ : CompleteLocalSAlgebra.Hom B A) : Prop :=
  ∃ (r : ℕ) (h : A.carrier →+* MvPowerSeries (Fin r) A.carrier)
    (k : MvPowerSeries (Fin r) A.carrier →+* B.carrier),
    IsLocalHom h ∧ IsLocalHom k ∧
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
        IsLocalHom h ∧ IsLocalHom k ∧
          k.comp MvPowerSeries.C = φ.hom ∧
          k.comp h = ψ.hom ∧
            MvPowerSeries.constantCoeff.comp h = RingHom.id A.carrier := Iff.rfl

/-- Formally homotopic maps extend a given minimal prime to the same ideal. -/
theorem FormallyHomotopic.extendsMinimalPrime_eq {A B : CompleteLocalSAlgebra S}
    {φ ψ : CompleteLocalSAlgebra.Hom B A} (h : FormallyHomotopic φ ψ)
    {Z : irreducibleComponents (PrimeSpectrum A.carrier)}
    {W W' : irreducibleComponents (PrimeSpectrum B.carrier)} :
    ExtendsMinimalPrime φ Z W → ExtendsMinimalPrime ψ Z W' → W = W' := sorry


variable {X : GroupoidsOver S} [hX : AlgebraicStack X] [hft : IsLocallyOfFiniteType X]

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
        ∃ f : GroupoidsOver.FormalObject.Hom η ξ, f.base.hom = φ.hom := Iff.rfl

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
          IsObjectComparison η ξ φ ∧ ExtendsMinimalPrime φ W Z := Iff.rfl

/-- Identification of irreducible components is reflexive. -/
theorem Identified.refl (ξ : GroupoidsOver.FormalObject X)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) :
    Identified ξ ξ Z Z := sorry

/-- Identification of irreducible components is symmetric. -/
theorem Identified.symm {ξ η : GroupoidsOver.FormalObject X}
    {Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)}
    {W : irreducibleComponents (PrimeSpectrum η.base.carrier)} :
    Identified ξ η Z W → Identified η ξ W Z := fun h => h.elim Or.inr Or.inl

variable (x0 : FieldValuedPoint X) [hx0 : AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]

/-- A power-series comparison of marked formal objects preserves the specified residue isomorphisms. -/
def IsPointedObjectComparison (ξ η : GroupoidsOver.FormalObject X)
    (mξ : StageOneMarking x0 ξ) (mη : StageOneMarking x0 η)
    (φ : CompleteLocalSAlgebra.Hom η.base ξ.base) : Prop :=
  IsPowerSeriesExtension φ ∧
    ∃ f : GroupoidsOver.FormalObject.Hom η ξ,
      f.base.hom = φ.hom ∧ mη.iso.hom ≫ f.app 0 = mξ.iso.hom

/-- Two marked components are identified by a marking-preserving power-series comparison
in either direction that extends their minimal primes. -/
def PointedIdentified (ξ η : GroupoidsOver.FormalObject X)
    (mξ : StageOneMarking x0 ξ) (mη : StageOneMarking x0 η)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier))
    (W : irreducibleComponents (PrimeSpectrum η.base.carrier)) : Prop :=
  (∃ φ : CompleteLocalSAlgebra.Hom η.base ξ.base,
    IsPointedObjectComparison x0 ξ η mξ mη φ ∧ ExtendsMinimalPrime φ Z W) ∨
  ∃ φ : CompleteLocalSAlgebra.Hom ξ.base η.base,
    IsPointedObjectComparison x0 η ξ mη mξ φ ∧ ExtendsMinimalPrime φ W Z

include hX hft hx0 in
/-- Marked component identification is reflexive. -/
theorem PointedIdentified.refl (ξ : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ] (mξ : StageOneMarking x0 ξ)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) :
    PointedIdentified x0 ξ ξ mξ mξ Z Z := sorry

/-- Marked component identification is symmetric. -/
theorem PointedIdentified.symm {ξ η : GroupoidsOver.FormalObject X}
    {mξ : StageOneMarking x0 ξ} {mη : StageOneMarking x0 η}
    {Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)}
    {W : irreducibleComponents (PrimeSpectrum η.base.carrier)} :
    PointedIdentified x0 ξ η mξ mη Z W → PointedIdentified x0 η ξ mη mξ W Z :=
  fun h => h.elim Or.inr Or.inl

/-- A finite-variable power-series extension gives a bijective correspondence of minimal-prime components. -/
theorem IsPowerSeriesExtension.existsUnique_extendsMinimalPrime
    {A A' : CompleteLocalSAlgebra S} {φ : CompleteLocalSAlgebra.Hom A' A}
    (hφ : IsPowerSeriesExtension φ) :
    (∀ Z : irreducibleComponents (PrimeSpectrum A.carrier),
      ∃! W : irreducibleComponents (PrimeSpectrum A'.carrier), ExtendsMinimalPrime φ Z W) ∧
    (∀ W : irreducibleComponents (PrimeSpectrum A'.carrier),
      ∃! Z : irreducibleComponents (PrimeSpectrum A.carrier), ExtendsMinimalPrime φ Z W) := sorry

include hX hft hx0 in
/-- Any two marked versal formal objects at a finite type point have a pointed
power-series comparison in one of the two directions. -/
theorem exists_pointedObjectComparison_or
    (ξ η : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ] [GroupoidsOver.FormalObject.IsVersal η]
    (mξ : StageOneMarking x0 ξ) (mη : StageOneMarking x0 η) :
    (∃ φ : CompleteLocalSAlgebra.Hom η.base ξ.base,
      IsPointedObjectComparison x0 ξ η mξ mη φ) ∨
    (∃ φ : CompleteLocalSAlgebra.Hom ξ.base η.base,
      IsPointedObjectComparison x0 η ξ mη mξ φ) := sorry

include hX hft hx0 in
/-- Pointed comparisons of the same marked versal formal objects are formally homotopic. -/
theorem isObjectComparison_formallyHomotopic
    {ξ η : GroupoidsOver.FormalObject X}
    [GroupoidsOver.FormalObject.IsVersal ξ] [GroupoidsOver.FormalObject.IsVersal η]
    (mξ : StageOneMarking x0 ξ) (mη : StageOneMarking x0 η)
    {φ ψ : CompleteLocalSAlgebra.Hom η.base ξ.base}
    (hφ : IsPointedObjectComparison x0 ξ η mξ mη φ)
    (hψ : IsPointedObjectComparison x0 ξ η mξ mη ψ) :
    FormallyHomotopic φ ψ := sorry

include hX hft hx0 in
/-- Components of a fixed marked versal formal object are identified exactly when equal. -/
theorem identified_self_iff (ξ : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ] (mξ : StageOneMarking x0 ξ)
    (Z W : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) :
    PointedIdentified x0 ξ ξ mξ mξ Z W ↔ Z = W := sorry

include hX hft hx0 in
/-- Pointed identification of marked versal components is transitive. -/
theorem PointedIdentified.trans {ξ η ζ : GroupoidsOver.FormalObject X}
    [GroupoidsOver.FormalObject.IsVersal ξ] [GroupoidsOver.FormalObject.IsVersal η]
    [GroupoidsOver.FormalObject.IsVersal ζ]
    {mξ : StageOneMarking x0 ξ} {mη : StageOneMarking x0 η} {mζ : StageOneMarking x0 ζ}
    {Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)}
    {W : irreducibleComponents (PrimeSpectrum η.base.carrier)}
    {Y : irreducibleComponents (PrimeSpectrum ζ.base.carrier)} :
    PointedIdentified x0 ξ η mξ mη Z W → PointedIdentified x0 η ζ mη mζ W Y →
      PointedIdentified x0 ξ ζ mξ mζ Z Y := sorry

namespace FormalBranches

/-- A branch representative consists of a versal formal object, an actual residue marking,
and an irreducible component of its base spectrum. -/
abbrev BranchRep {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom] :
    Type (u + 1) :=
  (ξ : GroupoidsOver.FormalObject X) ×
    PSigma fun _ : GroupoidsOver.FormalObject.IsVersal ξ =>
      StageOneMarking x0 ξ × irreducibleComponents (PrimeSpectrum ξ.base.carrier)

/-- Pack a marked versal component as a branch representative. -/
def BranchRep.mk (ξ : GroupoidsOver.FormalObject X)
    [hversal : GroupoidsOver.FormalObject.IsVersal ξ] (mξ : StageOneMarking x0 ξ)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) : BranchRep x0 :=
  ⟨ξ, ⟨hversal, ⟨mξ, Z⟩⟩⟩

/-- Packing a representative preserves its formal object. -/
theorem BranchRep.mk_fst (ξ : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ] (mξ : StageOneMarking x0 ξ)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) :
    (BranchRep.mk x0 ξ mξ Z).1 = ξ := sorry

end FormalBranches

/-- Formal branches through a finite type field-valued point are marked versal
components modulo marking-preserving power-series comparisons. -/
def FormalBranches {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom] :
    Type (u + 1) :=
  Quot fun (r r' : FormalBranches.BranchRep x0) =>
    PointedIdentified x0 r.1 r'.1 r.2.2.1 r'.2.2.1 r.2.2.2 r'.2.2.2

namespace FormalBranches

/-- Construct the formal branch of a marked versal component. -/
def mk (ξ : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ] (mξ : StageOneMarking x0 ξ)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) : FormalBranches x0 :=
  Quot.mk _ (BranchRep.mk x0 ξ mξ Z)

/-- Two marked versal components define the same branch exactly when pointed comparisons identify them. -/
theorem mk_eq_mk_iff {ξ η : GroupoidsOver.FormalObject X}
    [GroupoidsOver.FormalObject.IsVersal ξ] [GroupoidsOver.FormalObject.IsVersal η]
    (mξ : StageOneMarking x0 ξ) (mη : StageOneMarking x0 η)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier))
    (W : irreducibleComponents (PrimeSpectrum η.base.carrier)) :
    mk x0 ξ mξ Z = mk x0 η mη W ↔ PointedIdentified x0 ξ η mξ mη Z W := sorry

/-- Every fixed marked versal formal object represents each formal branch by a unique component. -/
theorem spec (ξ : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ] (mξ : StageOneMarking x0 ξ) :
    Function.Surjective (mk x0 ξ mξ) ∧
      ∀ Z W, mk x0 ξ mξ Z = mk x0 ξ mξ W ↔ Z = W := sorry

end FormalBranches

end AlgebraicGeometry.AlgebraicStack
