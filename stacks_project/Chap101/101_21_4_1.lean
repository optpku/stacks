/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicStack.InvariantSpectrum
import Mathlib.Algebra.Field.Subfield.Basic
import StacksCheckRecall

/-!
# The invariant-spectrum morphism of a special presentation

The field of invariant functions gives the displayed morphism
`Spec(k₀) = U/P ⟶ [U/R] ⟶ Z`.
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

variable {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
variable (P G : GroupoidScheme S)
variable {A B : Type u} [Field A] [CommRing B] [Algebra A B]
variable (tSharp : A →+* B)
variable (eU : Spec (CommRingCat.of A) ≅ P.U.left)
variable (eR : Spec (CommRingCat.of B) ≅ P.R.left)
variable
  (h_source : eR.hom ≫ P.s.left =
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
variable
  (h_target : eR.hom ≫ P.t.left =
    Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
variable [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
variable [IsEquivalenceRelation P.t P.s]
variable (hU : P.U = G.U)

variable (ι : GroupoidScheme.Hom P G) (hι : ι.IsIdentityOnObjects hU)
variable (f_can : SmallQuotient.quotientStack (ofScheme G) ⟶ Z)
variable [(toBasedFunctor f_can).IsEquivalence]

/- 101.21.4.1: The displayed morphism from Spec(k₀) = U/P through the quotient stack
and its established presentation equivalence to Z. -/
@[stacks 06N1] #check
  (AlgebraicGeometry.AlgebraicStack.etaleCovering P G tSharp eU eR h_source h_target
    hU ι hι f_can :
    GroupoidsOver.slice (invariantSpectrum P tSharp eU eR h_source h_target) ⟶ Z)

#check (AlgebraicGeometry.AlgebraicStack.etaleCovering_spec P G tSharp eU eR
    h_source h_target hU ι hι f_can :
  Nonempty
    (overMap (GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target) ≫
        AlgebraicGeometry.AlgebraicStack.etaleCovering P G tSharp eU eR h_source h_target
          hU ι hι f_can ≅
      atlasFromSlice_eqToHom P G hU ≫ f_can))

#check (RingHom.eqLocusField tSharp (algebraMap A B) : Subfield A)

#check (AlgebraicGeometry.GroupoidScheme.invariantSpectrumOver_left P tSharp eU
    (GroupoidScheme.invariantSpectrumMap_effectiveEpi P tSharp eU eR h_source h_target)
    (GroupoidScheme.invariantSpectrumMap_respectsBase P tSharp eU eR h_source h_target) :
  (invariantSpectrum P tSharp eU eR h_source h_target).left =
    Spec (CommRingCat.of (RingHom.eqLocus tSharp (algebraMap A B))))

#check (AlgebraicGeometry.GroupoidScheme.invariantKernelPairComparison_isIso P tSharp eU eR
    h_source h_target :
  IsIso
    (P.toPreRelation.kernelPairLift
      (GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target)
      (GroupoidScheme.invariantSpectrumQuotientMap_equalizes P tSharp eU
        (GroupoidScheme.invariantSpectrumMap_effectiveEpi P tSharp eU eR h_source h_target)
        (GroupoidScheme.invariantSpectrumMap_respectsBase P tSharp eU eR h_source h_target))))
