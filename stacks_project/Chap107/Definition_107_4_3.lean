/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IrreducibleComponent.Multiplicity
public import stacks_project.Chap107.Definition_107_4_1_FormalBranches
public import stacks_project.Chap107.Definition_107_4_1_VersalRing

/-!
# Multiplicity of a formal branch

The multiplicity of a formal branch of an algebraic stack through a finite-type
field-valued point is the multiplicity of the corresponding irreducible component
of the spectrum of any versal ring at that point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open FiberedCategoryOver.Groupoids
open TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- Irreducible components of `Spec (CommRingCat.of A.carrier)` are those of
`PrimeSpectrum A.carrier`, by `AlgebraicGeometry.Spec_carrier`. -/
theorem irreducibleComponents_spec (A : CompleteLocalSAlgebra S) :
    irreducibleComponents (Spec (CommRingCat.of A.carrier)) =
      irreducibleComponents (PrimeSpectrum A.carrier) :=
  sorry

/-- View a component of `Spec A` as a component of `PrimeSpectrum A` along
`AlgebraicGeometry.Spec_carrier`. -/
def toPrimeSpectrumComponent (A : CompleteLocalSAlgebra S)
    (Z : irreducibleComponents (Spec (CommRingCat.of A.carrier))) :
    irreducibleComponents (PrimeSpectrum A.carrier) :=
  Z

/-- View a component of `PrimeSpectrum A` as a component of `Spec A` along
`AlgebraicGeometry.Spec_carrier`. -/
def ofPrimeSpectrumComponent (A : CompleteLocalSAlgebra S)
    (Z : irreducibleComponents (PrimeSpectrum A.carrier)) :
    irreducibleComponents (Spec (CommRingCat.of A.carrier)) :=
  Z

/-- `toPrimeSpectrumComponent` is inverse to `ofPrimeSpectrumComponent`. -/
theorem toPrimeSpectrumComponent_ofPrimeSpectrumComponent (A : CompleteLocalSAlgebra S)
    (Z : irreducibleComponents (PrimeSpectrum A.carrier)) :
    toPrimeSpectrumComponent A (ofPrimeSpectrumComponent A Z) = Z :=
  sorry

/-- `ofPrimeSpectrumComponent` is inverse to `toPrimeSpectrumComponent`. -/
theorem ofPrimeSpectrumComponent_toPrimeSpectrumComponent (A : CompleteLocalSAlgebra S)
    (Z : irreducibleComponents (Spec (CommRingCat.of A.carrier))) :
    ofPrimeSpectrumComponent A (toPrimeSpectrumComponent A Z) = Z :=
  sorry

/-- Definition 107.4.3: the multiplicity of a formal branch of an algebraic stack `X`
locally of finite type over a locally Noetherian scheme `S`, through a finite-type
field-valued point `x0`, is the multiplicity of the corresponding irreducible
component of `Spec (CommRingCat.of A.carrier)` for any versal ring `A` to `X` at
`x0`. -/
@[stacks 0DRC]
noncomputable def formalBranchMultiplicity
    {X : GroupoidsOver S} [AlgebraicStack X]
    [LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A]
    (Z : irreducibleComponents (Spec (CommRingCat.of A.carrier))) : ℕ :=
  Scheme.irreducibleComponentMultiplicity (Spec (CommRingCat.of A.carrier)) Z

/-- `formalBranchMultiplicity` is the scheme-theoretic multiplicity of the corresponding
irreducible component of `Spec (CommRingCat.of A.carrier)`. -/
theorem formalBranchMultiplicity_eq
    {X : GroupoidsOver S} [AlgebraicStack X]
    [LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A]
    (Z : irreducibleComponents (Spec (CommRingCat.of A.carrier))) :
    formalBranchMultiplicity x0 A Z =
      Scheme.irreducibleComponentMultiplicity (Spec (CommRingCat.of A.carrier)) Z :=
  sorry

/-- The multiplicity of a formal branch coerces to the length of the local ring of
`Spec (CommRingCat.of A.carrier)` at the generic point of the corresponding
irreducible component. -/
theorem coe_formalBranchMultiplicity
    {X : GroupoidsOver S} [AlgebraicStack X]
    [LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A]
    (Z : irreducibleComponents (Spec (CommRingCat.of A.carrier))) :
    (formalBranchMultiplicity x0 A Z : ℕ∞) =
      Module.length
        ((Spec (CommRingCat.of A.carrier)).presheaf.stalk Z.2.1.genericPoint)
        ((Spec (CommRingCat.of A.carrier)).presheaf.stalk Z.2.1.genericPoint) :=
  sorry

/-- A power-series extension of versal rings that carries one minimal prime onto
the other preserves the multiplicity of the corresponding formal branch. -/
theorem formalBranchMultiplicity_extendsMinimalPrime
    {X : GroupoidsOver S} [AlgebraicStack X]
    [LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    {A A' : CompleteLocalSAlgebra S} [IsVersalRing x0 A] [IsVersalRing x0 A']
    (φ : CompleteLocalSAlgebra.Hom A' A) (hφ : IsPowerSeriesExtension φ)
    (Z : irreducibleComponents (Spec (CommRingCat.of A.carrier)))
    (W : irreducibleComponents (Spec (CommRingCat.of A'.carrier)))
    (hZW : ExtendsMinimalPrime φ (toPrimeSpectrumComponent A Z)
      (toPrimeSpectrumComponent A' W)) :
    formalBranchMultiplicity x0 A' W = formalBranchMultiplicity x0 A Z :=
  sorry

/-- Identified irreducible components of versal rings, in either power-series
direction, have the same formal-branch multiplicity. -/
theorem formalBranchMultiplicity_identified
    {X : GroupoidsOver S} [AlgebraicStack X]
    [LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A A' : CompleteLocalSAlgebra S) [IsVersalRing x0 A] [IsVersalRing x0 A']
    (Z : irreducibleComponents (Spec (CommRingCat.of A.carrier)))
    (W : irreducibleComponents (Spec (CommRingCat.of A'.carrier)))
    (h : Identified A A' (toPrimeSpectrumComponent A Z)
      (toPrimeSpectrumComponent A' W)) :
    formalBranchMultiplicity x0 A' W = formalBranchMultiplicity x0 A Z :=
  sorry

end AlgebraicGeometry.AlgebraicStack
