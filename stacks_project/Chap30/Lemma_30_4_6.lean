/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.AffineBase
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

universe u

/- Lemma 30.4.6: let `f : X ⟶ S` be a quasi-separated and quasi-compact morphism of
schemes, with `S` affine. For any quasi-coherent `𝒪_X`-module `ℱ`, the
degree-`q` global cohomology of `ℱ` on `X` is isomorphic to the degree-zero global
cohomology on `S` of the higher direct image `R^q f_* ℱ`. -/
@[stacks 01XK] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.globalCohomology_iso_degreeZero :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [QuasiCompact f] [QuasiSeparated f] [IsAffine S]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (q : ℕ),
      IsIsomorphic
        (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' q (⊤ : Opens X))
        (((SheafOfModules.toSheaf S.ringCatSheaf).obj
          (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ q)).H'
            0 (⊤ : Opens S)))
