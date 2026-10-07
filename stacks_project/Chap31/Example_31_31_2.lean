module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.IdealClosure.WeightedExample
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.ClosedSubscheme
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

universe u v

/- Example 31.31.2: for `ℚ[x, y]` with weights two and three, the projective closure of
`(y ^ 2)` is `(y)`, but `(y)` is not the irrelevant-ideal saturation of `(y ^ 2)`. -/
@[stacks 0BXK] #check (AlgebraicGeometry.WeightedProjExample.spec :
  AlgebraicGeometry.projClosedSubschemeIdeal
      AlgebraicGeometry.WeightedProjExample.grading
      AlgebraicGeometry.WeightedProjExample.ideal =
    AlgebraicGeometry.WeightedProjExample.lineIdeal ∧
  AlgebraicGeometry.WeightedProjExample.lineIdeal.toIdeal ≠
    AlgebraicGeometry.projSaturation
      AlgebraicGeometry.WeightedProjExample.grading
      AlgebraicGeometry.WeightedProjExample.ideal)

/- The degree-one formula for the ideal recovered from a homogeneous projective subscheme. -/
#check (AlgebraicGeometry.projClosedSubschemeIdeal_eq_degreeOneSaturation :
  ∀ {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsNoetherianRing A],
    GradedAlgebra.GeneratedBy 𝒜 1 → ∀ I : HomogeneousIdeal 𝒜,
      (AlgebraicGeometry.projClosedSubschemeIdeal 𝒜 I : Set A) =
        AlgebraicGeometry.projDegreeOneSaturationSet 𝒜 I.toIdeal)

/- The saturated homogeneous ideals are exactly the fixed points of projective closure. -/
#check (AlgebraicGeometry.projClosedSubschemeIdeal_eq_self_iff_saturated :
  ∀ {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsNoetherianRing A],
    GradedAlgebra.GeneratedBy 𝒜 1 → ∀ I : HomogeneousIdeal 𝒜,
      AlgebraicGeometry.projClosedSubschemeIdeal 𝒜 I = I ↔
        I.toIdeal = AlgebraicGeometry.projSaturation 𝒜 I)

/- The general formula uses the period of an explicit family of positive homogeneous
generators. -/
#check (AlgebraicGeometry.projClosedSubschemeIdeal_eq_degreeMultipleClosure :
  ∀ {A : Type v} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    [IsNoetherianRing A] (G : GradedAlgebra.PositiveGenerators 𝒜)
      (I : HomogeneousIdeal 𝒜),
        (AlgebraicGeometry.projClosedSubschemeIdeal 𝒜 I : Set A) =
          AlgebraicGeometry.projDegreeMultipleClosureSet 𝒜 I.toIdeal
            G.period)

/- A closed subscheme of a quasi-compact relative projective spectrum has the canonical
quotient presentation determined by its restricted ambient twists. -/
#check
  (AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation.existsClosedSubschemeQuotientPresentation :
    ∀ {S X Z : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
      (hqc : 𝒜.IsQuasicoherent)
      (A σ : S.affineOpens → Type u)
      [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
      [∀ U, AddSubgroupClass (σ U) (A U)]
      (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
      [∀ U, GradedRing (sectionGrading U)]
      (P : ∀ U : S.affineOpens, AlgebraicGeometry.ProjTwistPresentation (sectionGrading U))
      (model : ∀ (U : S.affineOpens) (d : ℕ),
        (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d)
      (presentation : AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation
        𝒜 A σ sectionGrading P model p)
      (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
      [AlgebraicGeometry.QuasiCompact p],
      Nonempty
        (AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation.CanonicalClosedSubschemeQuotient
          presentation i))

/- The positive homogeneous generators in the weighted example have period six. -/
#check (AlgebraicGeometry.WeightedProjExample.generators_period :
  AlgebraicGeometry.WeightedProjExample.generators.period = 6)

/- The monomials `x ^ n * y` witness the failure of ordinary saturation. -/
#check (AlgebraicGeometry.WeightedProjExample.x_pow_y_not_mem_ySquared :
  ∀ n : ℕ, AlgebraicGeometry.WeightedProjExample.x ^ n *
    AlgebraicGeometry.WeightedProjExample.y ∉
      AlgebraicGeometry.WeightedProjExample.ideal.toIdeal)
