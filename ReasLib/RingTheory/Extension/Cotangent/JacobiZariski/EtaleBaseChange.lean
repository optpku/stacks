/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.JacobiZariski.FilteredColimit
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.RingHom.IndEtale.Colimit
public import ReasLib.RingTheory.Kaehler.Unramified
import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale base change for the naive cotangent complex

This leaf owns the cohomology comparison maps for a compatible square of ring
maps. It records their invariance under ind-etale source and target changes and
specializes the result to henselizations and strict henselizations.

@stack 0D08
-/

@[expose] public section

open Algebra
open scoped TensorProduct

universe u v

noncomputable section

namespace Algebra.H1Cotangent

/-- The degree `-1` comparison
`H1(NL(B / A) ⊗[B] Bh) ⟶ H1Cotangent Ah Bh` attached to a compatible square. -/
@[stacks 0D08 "degree -1 cotangent base-change comparison"]
noncomputable abbrev presentationBaseChangeComparison
    (A Ah B Bh : Type u)
    [CommRing A] [CommRing Ah] [CommRing B] [CommRing Bh]
    [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
    [IsScalarTower A B Bh] [IsScalarTower A Ah Bh]
    {ι : Type v} (P : Generators A B ι) :
    LinearMap.ker (LinearMap.baseChange Bh P.toExtension.cotangentComplex) →ₗ[Bh]
      H1Cotangent Ah Bh :=
  (map A Ah Bh Bh).comp (tensor_presentation_cotangent_h1_to_h1_cotangent Bh P)

/-- Ind-etale changes on both sides make the degree `-1` naive-cotangent comparison bijective. -/
@[stacks 0D08 "degree -1 comparison under ind-etale base change"]
theorem presentationBaseChangeComparison_bijective_of_indEtale
    {A Ah B Bh : Type u}
    [CommRing A] [CommRing Ah] [CommRing B] [CommRing Bh]
    [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
    [IsScalarTower A B Bh] [IsScalarTower A Ah Bh]
    (hAh : RingHom.IndEtale (algebraMap A Ah))
    (hBh : RingHom.IndEtale (algebraMap B Bh)) :
    Function.Bijective
      (presentationBaseChangeComparison A Ah B Bh (Generators.self A B)) := sorry

end Algebra.H1Cotangent

namespace KaehlerDifferential

/-- The degree `0` comparison `Bh ⊗[B] Ω[B⁄A] ⟶ Ω[Bh⁄Ah]` attached to a compatible square. -/
@[stacks 0D08 "degree 0 cotangent base-change comparison"]
noncomputable abbrev baseChangeComparison
    (A Ah B Bh : Type u)
    [CommRing A] [CommRing Ah] [CommRing B] [CommRing Bh]
    [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
    [IsScalarTower A B Bh] [IsScalarTower A Ah Bh] :
    Bh ⊗[B] Ω[B⁄A] →ₗ[Bh] Ω[Bh⁄Ah] :=
  (map A Ah Bh Bh).comp (mapBaseChange A B Bh)

/-- Ind-etale changes on both sides make the degree `0` naive-cotangent comparison bijective. -/
@[stacks 0D08 "degree 0 comparison under ind-etale base change"]
theorem baseChangeComparison_bijective_of_indEtale
    {A Ah B Bh : Type u}
    [CommRing A] [CommRing Ah] [CommRing B] [CommRing Bh]
    [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
    [IsScalarTower A B Bh] [IsScalarTower A Ah Bh]
    (hAh : RingHom.IndEtale (algebraMap A Ah))
    (hBh : RingHom.IndEtale (algebraMap B Bh)) :
    Function.Bijective (baseChangeComparison A Ah B Bh) := sorry

end KaehlerDifferential

section Henselization

variable {A B Ah Bh : Type u}
variable [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
variable [CommRing Bh] [Algebra B Bh] [IsHenselizationOf B Bh]
variable [Algebra A Bh] [Algebra Ah Bh]
variable [IsScalarTower A B Bh] [IsScalarTower A Ah Bh]

/-- Lemma 15.33.8 (1), tag `0D08`: the comparison on
`H^{-1}` for the map induced on henselizations is bijective. -/
@[stacks 0D08 "(1)"]
theorem Algebra.H1Cotangent.presentationBaseChangeComparison_bijective_of_henselization :
    Function.Bijective
      (Algebra.H1Cotangent.presentationBaseChangeComparison
        A Ah B Bh (Generators.self A B)) := sorry

/-- Lemma 15.33.8 (2), tag `0D08`: the comparison on
`H^0 = Ω` for the map induced on henselizations is bijective. -/
@[stacks 0D08 "(2)"]
theorem KaehlerDifferential.baseChangeComparison_bijective_of_henselization :
    Function.Bijective (KaehlerDifferential.baseChangeComparison A Ah B Bh) := sorry

end Henselization

section StrictHenselization

variable {A B Ash Bsh : Type u}
variable [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
variable [CommRing Bsh] [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
variable [Algebra A Bsh] [Algebra Ash Bsh]
variable [IsScalarTower A B Bsh] [IsScalarTower A Ash Bsh]

/-- Lemma 15.33.8 (3), tag `0D08`: the comparison on
`H^{-1}` for the map induced on strict henselizations is bijective. -/
@[stacks 0D08 "(3)"]
theorem Algebra.H1Cotangent.presentationBaseChangeComparison_bijective_of_strictHenselization :
    Function.Bijective
      (Algebra.H1Cotangent.presentationBaseChangeComparison
        A Ash B Bsh (Generators.self A B)) := sorry

/-- Lemma 15.33.8 (4), tag `0D08`: the comparison on
`H^0 = Ω` for the map induced on strict henselizations is bijective. -/
@[stacks 0D08 "(4)"]
theorem KaehlerDifferential.baseChangeComparison_bijective_of_strictHenselization :
    Function.Bijective (KaehlerDifferential.baseChangeComparison A Ash B Bsh) := sorry

end StrictHenselization
