/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.AffineQuadruple
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Functor

/-!
# Canonical affine relative-Proj presentation

The ambient scheme is Proj of the actual section algebra. Its degree charts
are the actual degree opens, classified by the actual universal quadruples.
This supplies a concrete constructor of the strengthened RelativeProj owner.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite
open SheafOfModules.RingedSite
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.RelativeProjAffineSectionRing

variable {S : Scheme.{u}} (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
variable [𝒜.IsCommutative] [IsAffine S]

/-- The Yoneda sheaf of the actual Proj scheme. -/
def representedSheaf : Sheaf Scheme.zariskiTopology (Type u) :=
  ⟨yoneda.obj (scheme 𝒜), sorry⟩

/-- The chart inclusion is Yoneda of the actual open immersion. -/
def degreeInclusion (hA : 𝒜.IsQuasicoherent) (d : {n : ℕ // 1 ≤ n}) :
    (degreeFunctor 𝒜 hA d.2).toFunctor ⟶ (representedSheaf 𝒜).1 :=
  yoneda.map (Proj.degreeOpen (grading 𝒜) d.1).ι

/-- The canonical tensor-power transition classifies the same projective
point after inclusion. This is a property of the specified universal maps. -/
theorem degreeInclusion_transition (hA : 𝒜.IsQuasicoherent)
    (d e : {n : ℕ // 1 ≤ n}) (h : d.1 ∣ e.1) :
    (degreeAssociated 𝒜 hA d.2).transition (degreeAssociated 𝒜 hA e.2) h ≫
      degreeInclusion 𝒜 hA e = degreeInclusion 𝒜 hA d := sorry

/-- A coherent relative-Proj owner with actual scheme, charts, classifications
and chart maps; its remaining fields are geometric laws, not missing data. -/
@[implicit_reducible] def model (hA : 𝒜.IsQuasicoherent) : RelativeProjFunctor S 𝒜 where
  algebra_isQuasicoherent := hA
  toSheaf := representedSheaf 𝒜
  degreeFunctor d := degreeFunctor 𝒜 hA d.2
  degreeAssociated d := degreeAssociated 𝒜 hA d.2
  degreeFunctor_isRepresentable d := by
    change (yoneda.obj (chart 𝒜 d.1)).IsRepresentable
    infer_instance
  degreeToFunctor := degreeInclusion 𝒜 hA
  degreeToFunctor_transition := degreeInclusion_transition 𝒜 hA
  degreeToFunctor_isOpenImmersion := sorry
  coveredByDegree := sorry

/-- The model functor has the actual projective scheme as its values. -/
theorem model_toFunctor (hA : 𝒜.IsQuasicoherent) :
    (model 𝒜 hA).toFunctor = yoneda.obj (scheme 𝒜) := rfl

/-- The model's chart map is the specified geometric open inclusion. -/
theorem model_degreeInclusion (hA : 𝒜.IsQuasicoherent) (d : {n : ℕ // 1 ≤ n}) :
    (model 𝒜 hA).degreeToFunctor d =
      yoneda.map (Proj.degreeOpen (grading 𝒜) d.1).ι := rfl

end AlgebraicGeometry.Scheme.RelativeProjAffineSectionRing
