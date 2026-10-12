/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Flat
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.30.6: let `p : X ⟶ S` be presented as the relative projective spectrum of a
quasi-coherent graded `𝒪_S`-algebra. If its nonnegative degree pieces are flat for all
sufficiently large degrees, then `p` and every integral twist are flat over `S`. -/
@[stacks 0D4C] #check
  (AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation.flat_and_twist_flatOver_of_eventuallyFlatDegreePieces :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
      [𝒜.IsCommutative]
      {A σ : S.affineOpens → Type u}
      [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
      [∀ U, AddSubgroupClass (σ U) (A U)]
      {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
      [∀ U, GradedRing (sectionGrading U)]
      {P : ∀ U : S.affineOpens,
        AlgebraicGeometry.ProjTwistPresentation (sectionGrading U)}
      {model : ∀ (U : S.affineOpens) (d : ℕ),
        (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+
          sectionGrading U d}
      (hqc : 𝒜.IsQuasicoherent)
      (hModel : ∀ U : S.affineOpens,
        AlgebraicGeometry.AffineOpenSectionProj.IsAffineOpenSectionModel
          (sectionGrading U) 𝒜 U (model U))
      (presentation : AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation
        𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p),
      presentation.EventuallyFlatDegreePieces →
        AlgebraicGeometry.Flat p ∧
          ∀ d : ℤ, AlgebraicGeometry.Scheme.Modules.flatOver
            (presentation.twistAlgebra d) p)
