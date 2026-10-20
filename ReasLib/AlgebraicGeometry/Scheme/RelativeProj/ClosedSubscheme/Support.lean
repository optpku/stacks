module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.ClosedSubscheme

/-!
# Support of quotients defining closed subschemes of relative projective spectra

This file relates finite-degree quotient presentations of closed subschemes of relative
projective spectra to the support of the corresponding quotient module sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation

/-- A finitely presented closed subscheme of a quasi-compact relative projective spectrum that
avoids a compact open of the base is cut out in one positive degree by a finite-type
quasi-coherent subobject whose quotient is supported away from that open. -/
theorem existsQuotientByFiniteTypeDegreeSubobject_support_disjoint
    {S X Z : Scheme.{u}} {p : X ⟶ S}
    [CompactSpace S] [QuasiSeparatedSpace S]
    (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
    (hqc : 𝒜.IsQuasicoherent)
    (A σ : S.affineOpens → Type u)
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    (model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d)
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact p]
    [Scheme.Hom.FinitePresentation i]
    (hfinite : ∀ n : ℕ, (𝒜 (Int.ofNat n)).IsFiniteType)
    (U : S.Opens) (hU : IsCompact (U : Set S))
    (hdisjoint : Disjoint (U : Set S) (Set.range (i ≫ p).base)) :
    ∃ (d : ℕ) (F : Subobject (𝒜 (Int.ofNat d)))
      (Q : presentation.ClosedSubschemeQuotient i),
      0 < d ∧
        F ∈ Scheme.Modules.finiteTypeQuasiCoherentSubobjects (𝒜 (Int.ofNat d)) ∧
          Q.IsQuotientByDegreeSubobject d F ∧
            Disjoint (RingedSpace.moduleSupport (cokernel F.arrow)) (U : Set S) := sorry

end AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation
