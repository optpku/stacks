/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine

/-!
# Higher Direct Images over an Affine Base

This module records the comparison between global cohomology and degree-zero cohomology of
higher direct images for quasi-compact, quasi-separated morphisms with affine target.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HigherDirectImage

variable {X S : Scheme.{u}}

/-- For a quasi-compact, quasi-separated morphism with affine target, global cohomology is
isomorphic to the degree-zero global cohomology of the corresponding higher direct image. -/
@[stacks 01XK]
theorem globalCohomology_iso_degreeZero
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [IsAffine S]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (q : ℕ) :
    IsIsomorphic
      (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' q (⊤ : Opens X))
      (((SheafOfModules.toSheaf S.ringCatSheaf).obj
        (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ q)).H'
          0 (⊤ : Opens S)) := sorry

end AlgebraicGeometry.Scheme.HigherDirectImage
