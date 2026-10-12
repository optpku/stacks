/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Lemma_52_25_5_Sections
public import stacks_project.Chap52.Lemma_52_25_3_EulerCharacteristic
public import stacks_project.Chap52.Proposition_52_25_4_Tensor
public import ReasLib.RingTheory.Depth.RegularSequence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.CoherentTriple

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {S : CoherentTripleSetup A}

/-- The depth-three hypothesis makes the cokernel of the canonical section restriction map
finite-length over the local ring. -/
theorem globalSectionsRestriction_cokernel_finiteLength
    (L : CoherentTriple S) (hdepth : (3 : ℕ∞) ≤ moduleDepth A A) [L.IsInvertible] :
    IsFiniteLength A
      (Scheme.Hom.globalSectionsMod
          (S.closedFiberOnU ≫ S.algebraization.U.ι)
          (L.F₀.restrict S.algebraization.U₀.ι) ⧸
        LinearMap.range L.globalSectionsRestriction.hom) := sorry

/-- Lemma 52.25.5 (1): for an invertible coherent triple under the depth-three hypothesis, its
Euler characteristic is the `A`-length of the cokernel of restriction on global sections. -/
@[stacks 0F28]
theorem eulerCharacteristic_eq_cokernelLength
    (L : CoherentTriple S) (hdepth : (3 : ℕ∞) ≤ moduleDepth A A) [L.IsInvertible] :
    L.eulerCharacteristic =
      ((Module.length A
          (Scheme.Hom.globalSectionsMod
              (S.closedFiberOnU ≫ S.algebraization.U.ι)
              (L.F₀.restrict S.algebraization.U₀.ι) ⧸
            LinearMap.range L.globalSectionsRestriction.hom)).toNat : ℤ) := sorry

/-- Lemma 52.25.5 (2): the Euler characteristic of an invertible coherent triple is
nonnegative under the depth-three hypothesis. -/
@[stacks 0F28]
theorem eulerCharacteristic_nonneg
    (L : CoherentTriple S) (hdepth : (3 : ℕ∞) ≤ moduleDepth A A) [L.IsInvertible] :
    0 ≤ L.eulerCharacteristic := sorry

/-- Lemma 52.25.5 (3): under the depth-three hypothesis, vanishing Euler characteristic is
equivalent to the punctured component being isomorphic to the structure module. -/
@[stacks 0F28]
theorem eulerCharacteristic_eq_zero_iff_isoUnit
    (L : CoherentTriple S) (hdepth : (3 : ℕ∞) ≤ moduleDepth A A) [L.IsInvertible] :
    let U := S.algebraization.U
    L.eulerCharacteristic = 0 ↔
      Nonempty
        (L.F ≅
          (SheafOfModules.unit U.toScheme.ringCatSheaf : U.toScheme.Modules)) := sorry

end AlgebraicGeometry.CoherentTriple
