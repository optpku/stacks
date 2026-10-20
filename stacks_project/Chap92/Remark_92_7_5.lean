/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.StandardTriangle
public import stacks_project.Chap92.Remark_92_7_5_Resolution
import StacksCheckRecall

/-!
# Alternative construction of the fundamental triangle

Functorial standard resolutions over `A` give a differential short exact sequence
for an injective map `B → C`. Tensor base change computes the relative cotangent
complex, and the general case follows by passing through `B × C`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject
open Algebra.PolynomialSite

noncomputable section

universe u

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/- Remark 92.7.5: the differential short exact sequence of functorial standard
resolutions yields the fundamental triangle when the tower map is injective. -/
@[stacks 08SD] #check (Algebra.CotangentComplex.transitivityTriangle_iso_of_injective A B C :
  ∀ h_inj : Function.Injective (algebraMap B C),
    IsIsomorphic
      (DerivedCategory.triangleOfSES
        (Algebra.CotangentComplex.functorialOmegaCochainSequence_shortExact A B C h_inj))
      (Algebra.CotangentComplex.transitivityTriangle A B C))

/- Remark 92.7.5 (1): injectivity makes each target standard term polynomial over
its source standard term. Both displayed resolutions are over `A`. -/
@[stacks 08SD] #check (Algebra.CotangentComplex.isPolynomial_standardQ_over_standardP A B C :
  ∀ n : SimplexCategoryᵒᵖ, Function.Injective (algebraMap B C) →
    Algebra.IsPolynomial (Algebra.CotangentComplex.standardP A B n)
      (Algebra.CotangentComplex.standardQ A C n))

/- Remark 92.7.5 (2): reversal of arrows gives the cosimplicial polynomial squares. -/
@[stacks 08SD] #check (Algebra.CotangentComplex.tripleCosimplicial A B C :
  Function.Injective (algebraMap B C) → CosimplicialObject (Algebra.PolynomialTower A B C)ᵒᵖ)

/- Remark 92.7.5 (3): the tensor algebra and its canonical augmentation. -/
@[stacks 08SD] #check (Algebra.CotangentComplex.barQ A B C :
  SimplexCategoryᵒᵖ → Function.Injective (algebraMap B C) → Type u)
#check (Algebra.CotangentComplex.barQHom A B C :
  ∀ h_inj : Function.Injective (algebraMap B C),
    Algebra.CotangentComplex.barQSimplicial A B C h_inj ⟶
      (const (CommAlgCat.{u} B)).obj (CommAlgCat.of B C))

/- Remark 92.7.5 (4): the tensor augmentation is a resolution over `B`. -/
@[stacks 08SD] #check (Algebra.CotangentComplex.isResolution_barQHom A B C :
  ∀ h_inj : Function.Injective (algebraMap B C),
    IsResolution (Algebra.CotangentComplex.barQHom A B C h_inj))

variable (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C))

/- Remark 92.7.5 (5): the canonical differential sequence is short exact in every degree. -/
@[stacks 08SD] #check (Algebra.PolynomialTower.omegaSequence_app_shortExact A B C
    (Algebra.CotangentComplex.triple A B C n h_inj) :
  (Algebra.PolynomialTower.omegaSequence_app A B C
    (Algebra.CotangentComplex.triple A B C n h_inj)).ShortExact)
#check (Algebra.CotangentComplex.functorialOmegaCochainSequence_shortExact A B C :
  ∀ h_inj : Function.Injective (algebraMap B C),
    (Algebra.CotangentComplex.functorialOmegaCochainSequence A B C h_inj).ShortExact)

/- Remark 92.7.5 (6): the right differential complex represents the relative cotangent complex. -/
@[stacks 08SD] #check (Algebra.CotangentComplex.barQ_represents_relative A B C :
  ∀ h_inj : Function.Injective (algebraMap B C),
    IsIsomorphic (Algebra.CotangentComplex.derived B C)
      (DerivedCategory.Q.obj (Algebra.CotangentComplex.omegaBarQCochain A B C h_inj)))

/- Remark 92.7.5 (8): the product structure map is injective. -/
@[stacks 08SD] #check (Algebra.prod_algebraMap_injective B C :
  Function.Injective (algebraMap B (B × C)))

/- Remark 92.7.5 (9): the second product projection is flat. -/
@[stacks 08SD] #check (RingHom.flat_snd B C : (RingHom.snd B C).Flat)

/- Remark 92.7.5 (10): product comparison and extension along the second projection
recover the fundamental triangle for an arbitrary tower. -/
@[stacks 08SD] #check (Algebra.CotangentComplex.transitivityTriangle_iso_extend_prod A B C :
  IsIsomorphic
    (((ModuleCat.derivedExtensionOfScalars (RingHom.snd B C)).mapTriangle).obj
      (Algebra.CotangentComplex.transitivityTriangle A B (B × C)))
    (Algebra.CotangentComplex.transitivityTriangle A B C))
