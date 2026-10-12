/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The coproduct of a finite standard affine covering is affine. -/
theorem standardCover_coproduct_isAffine
    (τ : StandardTopology) {T : Scheme.{u}}
    (family : AffineFamilyOver T) (hfamily : τ.IsCover family)
    [HasCoproduct family.U] :
    IsAffine (∐ family.U) := sorry

/-- The coproduct singleton of a finite standard affine covering is an fpqc covering. -/
theorem standardCover_coproduct_fpqcCovering
    (τ : StandardTopology) {T : Scheme.{u}}
    (family : AffineFamilyOver T) (hfamily : τ.IsCover family)
    [HasCoproduct family.U] :
    Scheme.FpqcCovering (fun _ : PUnit ↦ Over.mk (Sigma.desc family.map)) := sorry

/-- For a standard topology other than Zariski, the coproduct singleton of a finite
standard affine covering is a covering for that topology. -/
theorem standardCover_coproduct_covering
    (τ : StandardTopology) {T : Scheme.{u}}
    (family : AffineFamilyOver T) (hfamily : τ.IsCover family)
    [HasCoproduct family.U] (hτ : τ ≠ .zariski) :
    Presieve.ofArrows (fun _ : PUnit ↦ ∐ family.U)
      (fun _ ↦ Sigma.desc family.map) ∈ τ.precoverage.coverings T := sorry

end AlgebraicGeometry
