/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap101.«101_21_4_1_Covering»
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equation 101.21.4.1 — étale covering from the invariant spectrum

The displayed chain Spec(k₀) = Ū = U/P → [U/R] = Z is the canonical 1-morphism
from the invariant spectrum of the identity-component finite locally free
equivalence relation P ⊂ R to an algebraic stack Z, obtained by composing a
factorization `Ū ⟶ [U/R]` of the atlas of the presentation groupoid with an
equivalence `f_can : [U/R] ⟶ Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
variable (P G : GroupoidScheme S)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
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

/-- 101.21.4.1: The displayed chain Spec(k₀) = Ū = U/P → [U/R] = Z is the
canonical 1-morphism from the invariant spectrum of the identity-component
finite locally free equivalence relation P ⊂ R to the algebraic stack Z.
Equalities Spec(k₀) = Ū = U/P identify the domain with the invariant spectrum
of P; the arrow is the atlas factorization `Ū ⟶ [U/R]` composed with a
presentation equivalence `f_can : [U/R] ⟶ Z`. -/
@[stacks 06N1]
def etaleCovering
    (ι : GroupoidScheme.Hom P G) (hι : ι.IsIdentityOnObjects hU)
    (f_can : (ofScheme G).quotientStack ⟶ Z)
    [(toBasedFunctor f_can).IsEquivalence] :
    GroupoidsOver.slice (invariantSpectrum P tSharp eU eR h_source h_target) ⟶ Z :=
  invariantSpectrumToQuotient P G tSharp eU eR h_source h_target hU ι hι ≫ f_can

/-- The covering factors the atlas of `[U/R]` through the invariant-spectrum
quotient of P and then applies the equivalence `f_can`. -/
theorem etaleCovering_spec
    (ι : GroupoidScheme.Hom P G) (hι : ι.IsIdentityOnObjects hU)
    (f_can : (ofScheme G).quotientStack ⟶ Z)
    [(toBasedFunctor f_can).IsEquivalence] :
    Nonempty
      (overMap (invariantSpectrumQuotient P tSharp eU eR h_source h_target) ≫
          etaleCovering P G tSharp eU eR h_source h_target hU ι hι f_can ≅
        atlasFromSlice_eqToHom P G hU ≫ f_can) :=
  sorry

/-- The domain of the covering is the spectrum of the ring of invariant
functions of P. -/
theorem etaleCovering_domain :
    (invariantSpectrum P tSharp eU eR h_source h_target).left =
      Spec (CommRingCat.of (invariantFunctions tSharp)) :=
  sorry

/-- The kernel pair of `U ⟶ Ū` is the identity-component equivalence relation P. -/
theorem etaleCovering_kernelPair :
    IsIso
      (P.toPreRelation.kernelPairLift
        (invariantSpectrumQuotient P tSharp eU eR h_source h_target)
        (GroupoidScheme.invariantSpectrumQuotientMap_equalizes P tSharp eU
          (GroupoidScheme.invariantSpectrumMap_effectiveEpi P tSharp eU eR
            h_source h_target)
          (GroupoidScheme.invariantSpectrumMap_respectsBase P tSharp eU eR
            h_source h_target))) :=
  GroupoidScheme.invariantKernelPairComparison_isIso P tSharp eU eR h_source h_target

end AlgebraicGeometry.AlgebraicStack
