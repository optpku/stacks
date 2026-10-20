/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.Homology

/-!
# Intrinsic descent of divided powers to homology

The basic homology construction obtains divided powers from a fixed positive-acyclic surjective
cover.  This leaf records the resulting operation by a target-local cycle formula.  The formula
does not mention the cover and therefore gives the reusable comparison surface for changing
presentations, base-change models, or resolutions.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DirectSum

universe u v

namespace DividedPowerChainAlgebra

variable {R : Type u} [CommRing R]
variable {A B C : DividedPowerChainAlgebra.{u, v} R}

/-! ## The intrinsic cycle formula -/

/-- Apply a chain-level divided power to a specified positive-even cycle. -/
def gammaCycleValue (B : DividedPowerChainAlgebra.{u, v} R) (n d : ℕ)
    (x : B.toChainDGAlgebra.cycles (2 * (d + 1) : ℤ)) :
    B.toChainDGAlgebra.nonnegativePiece (2 * (n * (d + 1))) :=
  B.gamma.gammaPiece n d (B.toChainDGAlgebra.iCycles (2 * (d + 1)) x)

/-- The divided power of a positive-even cycle is again a cycle. -/
theorem gammaCycleValue_isCycle (B : DividedPowerChainAlgebra.{u, v} R) (n d : ℕ)
    (x : B.toChainDGAlgebra.cycles (2 * (d + 1) : ℤ)) :
    ((forget₂ (ModuleCat.{v} R) Ab).map
      (B.toChainDGAlgebra.toChainComplex.d
        (2 * (n * (d + 1)) : ℤ) ((2 * (n * (d + 1)) : ℕ) - 1)))
      (B.gammaCycleValue n d x) = 0 := sorry

/-- The divided power of a specified cycle, bundled in the canonical cycle object. -/
def gammaCycle (B : DividedPowerChainAlgebra.{u, v} R) (n d : ℕ)
    (x : B.toChainDGAlgebra.cycles (2 * (d + 1) : ℤ)) :
    B.toChainDGAlgebra.cycles (2 * (n * (d + 1)) : ℤ) :=
  B.toChainDGAlgebra.toChainComplex.cyclesMk
    (B.gammaCycleValue n d x) ((2 * (n * (d + 1)) : ℕ) - 1)
      (ChainDGAlgebra.down_next_ofNat (2 * (n * (d + 1))))
      (B.gammaCycleValue_isCycle n d x)

/-- The underlying homogeneous value of `gammaCycle` is the chain-level divided power. -/
@[simp]
theorem iCycles_gammaCycle (B : DividedPowerChainAlgebra.{u, v} R) (n d : ℕ)
    (x : B.toChainDGAlgebra.cycles (2 * (d + 1) : ℤ)) :
    B.toChainDGAlgebra.iCycles (2 * (n * (d + 1))) (B.gammaCycle n d x) =
      B.gammaCycleValue n d x := sorry

/-- The homology class represented by the divided power of a specified cycle. -/
def gammaHomologyClass (B : DividedPowerChainAlgebra.{u, v} R) (n d : ℕ)
    (x : B.toChainDGAlgebra.cycles (2 * (d + 1) : ℤ)) :
    B.toChainDGAlgebra.homologyPiece (2 * (n * (d + 1))) :=
  B.toChainDGAlgebra.homologyπ (2 * (n * (d + 1))) (B.gammaCycle n d x)

/-- A divided-power structure on `H(B)` is the intrinsic descent of the chain-level structure
when its value on every represented homogeneous class is represented by the corresponding
chain-level divided power. -/
@[stacks 09PK "intrinsic descent of divided powers to homology"]
def DescendsToHomology (B : DividedPowerChainAlgebra.{u, v} R)
    (gammaH : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart) : Prop :=
  ∀ (n d : ℕ) (x : B.toChainDGAlgebra.cycles (2 * (d + 1) : ℤ)),
    gammaH.gammaPiece n d
        (B.toChainDGAlgebra.homologyπ (2 * (d + 1)) x) =
      B.gammaHomologyClass n d x

namespace DescendsToHomology

/-- Intrinsic homology descent exposes its cycle-class computation rule. -/
theorem gammaPiece {gammaH : NonnegGradedAlgebra.DividedPowers
    B.toChainDGAlgebra.homologyNonnegativePart}
    (h : B.DescendsToHomology gammaH) (n d : ℕ)
    (x : B.toChainDGAlgebra.cycles (2 * (d + 1) : ℤ)) :
    gammaH.gammaPiece n d
        (B.toChainDGAlgebra.homologyπ (2 * (d + 1)) x) =
      B.gammaHomologyClass n d x := sorry

/-- The target-local cycle formula determines a divided-power structure on homology uniquely. -/
theorem unique
    {gammaH deltaH : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart}
    (hgamma : B.DescendsToHomology gammaH)
    (hdelta : B.DescendsToHomology deltaH) : gammaH = deltaH := sorry

end DescendsToHomology

namespace Hom

/-- The divided powers obtained from a positive-acyclic surjective cover satisfy the intrinsic
target cycle formula. -/
theorem dividedPowersOnHomology_descends (f : Hom A B)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes) (hf : f.Surjective) :
    B.DescendsToHomology (f.dividedPowersOnHomology hA hf) := sorry

/-- A fixed positive-acyclic surjective cover produces the unique divided-power structure on
target homology satisfying the intrinsic cycle formula. -/
@[stacks 09PK "unique intrinsic divided powers on homology"]
theorem existsUnique_descendsToHomology (f : Hom A B)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes) (hf : f.Surjective) :
    ∃! gammaH : NonnegGradedAlgebra.DividedPowers
        B.toChainDGAlgebra.homologyNonnegativePart,
      B.DescendsToHomology gammaH := sorry

/-- A divided-power structure on target homology satisfies the intrinsic cycle formula exactly
when it is the structure induced by a fixed positive-acyclic surjective cover. -/
theorem descendsToHomology_iff_eq (f : Hom A B)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes) (hf : f.Surjective)
    (gammaH : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart) :
    B.DescendsToHomology gammaH ↔
      gammaH = f.dividedPowersOnHomology hA hf := sorry

/-- The divided-power graded algebra on target homology supplied by a positive-acyclic
surjective cover.  Its operation is the explicit homology operation, while its specification is
the cover-independent intrinsic cycle formula. -/
@[stacks 09PK "bundled divided-power algebra on homology"]
def homologyDPAlgebra (f : Hom A B)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes) (hf : f.Surjective) :
    DividedPowerGradedAlgebra.{u, v} R :=
  DividedPowerGradedAlgebra.of B.toChainDGAlgebra.homologyNonnegativePart
    (f.dividedPowersOnHomology hA hf)

/-- The graded algebra underlying `homologyDPAlgebra` is the canonical homology algebra. -/
@[simp]
theorem homologyDPAlgebra_toGradedAlgebra (f : Hom A B)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes) (hf : f.Surjective) :
    (f.homologyDPAlgebra hA hf).toGradedAlgebra =
      B.toChainDGAlgebra.homologyNonnegativePart := sorry

/-- The divided powers carried by `homologyDPAlgebra` are the explicit operations induced by
the cover. -/
@[simp]
theorem homologyDPAlgebra_gamma (f : Hom A B)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes) (hf : f.Surjective) :
    (f.homologyDPAlgebra hA hf).gamma = f.dividedPowersOnHomology hA hf := sorry

/-- The divided powers in `homologyDPAlgebra` satisfy the target-local cycle formula. -/
@[simp]
theorem homologyDPAlgebra_gammaPiece (f : Hom A B)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes) (hf : f.Surjective)
    (n d : ℕ) (x : B.toChainDGAlgebra.cycles (2 * (d + 1) : ℤ)) :
    (f.homologyDPAlgebra hA hf).gamma.gammaPiece n d
        (B.toChainDGAlgebra.homologyπ (2 * (d + 1)) x) =
      B.gammaHomologyClass n d x := sorry

/-- Two positive-acyclic surjective presentations of the same target induce the same intrinsic
divided-power operations on its homology. -/
@[stacks 09PK "independence of the positive-acyclic presentation"]
theorem dividedPowersOnHomology_eq (f : Hom A B) (g : Hom C B)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hC : C.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) (hg : g.Surjective) :
    f.dividedPowersOnHomology hA hf = g.dividedPowersOnHomology hC hg := sorry

/-- The bundled divided-power homology algebra is independent of the chosen positive-acyclic
surjective presentation of its target. -/
@[stacks 09PK "presentation-independent divided-power homology algebra"]
theorem homologyDPAlgebra_eq (f : Hom A B) (g : Hom C B)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hC : C.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) (hg : g.Surjective) :
    f.homologyDPAlgebra hA hf = g.homologyDPAlgebra hC hg := sorry

end Hom

/-! ## Functoriality of intrinsic homology descent -/

/-- A chain-level divided-power morphism preserves the intrinsic divided-power formula on
homology whenever the source and target homology operations satisfy that formula. -/
theorem Hom.homologyHom_map_gamma
    (f : Hom A B)
    {gammaA : NonnegGradedAlgebra.DividedPowers
      A.toChainDGAlgebra.homologyNonnegativePart}
    {gammaB : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart}
    (hA : A.DescendsToHomology gammaA) (hB : B.DescendsToHomology gammaB)
    (n : ℕ) (x : A.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart) :
    f.toChainHom.homologyHom.evenMap (gammaA n x) =
      gammaB n (f.toChainHom.homologyHom.evenPositiveMap x) := sorry

/-- The map on homology induced by a divided-power chain-DGA morphism, bundled as a morphism of
the intrinsic divided-power graded algebras. -/
@[stacks 09PK "functoriality of intrinsic homology divided powers"]
def Hom.homologyDPHom
    (f : Hom A B)
    {gammaA : NonnegGradedAlgebra.DividedPowers
      A.toChainDGAlgebra.homologyNonnegativePart}
    {gammaB : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart}
    (hA : A.DescendsToHomology gammaA) (hB : B.DescendsToHomology gammaB) :
    DividedPowerGradedAlgebra.of A.toChainDGAlgebra.homologyNonnegativePart gammaA ⟶
      DividedPowerGradedAlgebra.of B.toChainDGAlgebra.homologyNonnegativePart gammaB where
  toGradedHom := f.toChainHom.homologyHom
  map_gamma := f.homologyHom_map_gamma hA hB

/-- The underlying graded map of `homologyDPHom` is the canonical map on homology. -/
@[simp]
theorem Hom.homologyDPHom_toGradedHom
    (f : Hom A B)
    {gammaA : NonnegGradedAlgebra.DividedPowers
      A.toChainDGAlgebra.homologyNonnegativePart}
    {gammaB : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart}
    (hA : A.DescendsToHomology gammaA) (hB : B.DescendsToHomology gammaB) :
    (f.homologyDPHom hA hB).toGradedHom = f.toChainHom.homologyHom := sorry

/-- On a homogeneous class, `homologyDPHom` is the canonical homology map. -/
@[simp]
theorem Hom.homologyDPHom_apply
    (f : Hom A B)
    {gammaA : NonnegGradedAlgebra.DividedPowers
      A.toChainDGAlgebra.homologyNonnegativePart}
    {gammaB : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart}
    (hA : A.DescendsToHomology gammaA) (hB : B.DescendsToHomology gammaB)
    (n : ℕ) (x : A.toChainDGAlgebra.homologyPiece n) :
    (f.homologyDPHom hA hB).toGradedHom.map n x =
      f.toChainHom.homologyLinearMap n x := sorry

/-- Intrinsic homology divided-power maps preserve identity morphisms. -/
@[simp]
theorem Hom.homologyDPHom_id
    (A : DividedPowerChainAlgebra.{u, v} R)
    {gammaA : NonnegGradedAlgebra.DividedPowers
      A.toChainDGAlgebra.homologyNonnegativePart}
    (hA : A.DescendsToHomology gammaA) :
    (Hom.id A).homologyDPHom hA hA =
      𝟙 (DividedPowerGradedAlgebra.of
        A.toChainDGAlgebra.homologyNonnegativePart gammaA) := sorry

/-- Intrinsic homology divided-power maps preserve composition. -/
@[simp]
theorem Hom.homologyDPHom_comp
    (f : Hom A B) (g : Hom B C)
    {gammaA : NonnegGradedAlgebra.DividedPowers
      A.toChainDGAlgebra.homologyNonnegativePart}
    {gammaB : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart}
    {gammaC : NonnegGradedAlgebra.DividedPowers
      C.toChainDGAlgebra.homologyNonnegativePart}
    (hA : A.DescendsToHomology gammaA) (hB : B.DescendsToHomology gammaB)
    (hC : C.DescendsToHomology gammaC) :
    (Hom.comp g f).homologyDPHom hA hC =
      f.homologyDPHom hA hB ≫ g.homologyDPHom hB hC := sorry

end DividedPowerChainAlgebra
