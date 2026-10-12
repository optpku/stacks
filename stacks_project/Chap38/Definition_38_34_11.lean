/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T]

/- Definition 38.34.11 (1): a finite affine family is an h covering exactly
when its maps are of finite presentation and a standard ph covering refines it. -/
@[stacks 0EUY] #check
  (AlgebraicGeometry.AffineFamilyOver.hCovering_iff_exists_standardPhRefinement :
    ∀ family : AlgebraicGeometry.AffineFamilyOver T,
      AlgebraicGeometry.Scheme.HCovering
          (fun i : Fin family.n ↦ Over.mk (family.map i)) ↔
        (∀ i, AlgebraicGeometry.Scheme.Hom.FinitePresentation (family.map i)) ∧
          ∃ cover : AlgebraicGeometry.StandardPhCovering T,
            Nonempty (AlgebraicGeometry.AffineFamilyOver.Refinement
              cover.toAffineFamily family))

/- Definition 38.34.11 (2): a finite affine family is an h covering exactly
when its maps are of finite presentation and it is a V covering. -/
@[stacks 0EUY] #check
  (AlgebraicGeometry.AffineFamilyOver.hCovering_iff_isVCovering :
    ∀ family : AlgebraicGeometry.AffineFamilyOver T,
      AlgebraicGeometry.Scheme.HCovering
          (fun i : Fin family.n ↦ Over.mk (family.map i)) ↔
        (∀ i, AlgebraicGeometry.Scheme.Hom.FinitePresentation (family.map i)) ∧
          AlgebraicGeometry.IsVCovering T family.U family.map)
