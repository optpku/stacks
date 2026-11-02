/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion.Exact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FiniteTypeGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.TwistGluing
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.ClosedImmersion

/-!
# Closed subschemes of relative projective spectra

This file records the canonical graded map obtained by restricting the twists of a relative
projective spectrum to a closed subscheme, together with its degreewise kernel.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AffineOpenSectionProj

variable {S : Scheme.{u}} (U : S.affineOpens)
variable {A B σ τ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable (𝒢 : ℕ → σ) (ℋ : ℕ → τ) [GradedRing 𝒢] [GradedRing ℋ]
variable (𝒜 ℬ : GradedAlgebraSheaf.{u, u} S.sheaf)
variable (modelA : ∀ d : ℕ,
  (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ 𝒢 d)
variable (modelB : ∀ d : ℕ,
  (ℬ (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ ℋ d)
variable (hModelA : IsAffineOpenSectionModel 𝒢 𝒜 U modelA)
variable (hModelB : IsAffineOpenSectionModel ℋ ℬ U modelB)

/-- Transport a graded sheaf map to genuine affine section-ring models. The underlying
function sums the images of the homogeneous components; no existence theorem is used to
choose a ring map. -/
noncomputable def mapOnSections
    (hModelA : IsAffineOpenSectionModel 𝒢 𝒜 U modelA)
    (hModelB : IsAffineOpenSectionModel ℋ ℬ U modelB)
    (q : 𝒜 ⟶ ℬ) : 𝒢 →+*ᵍ ℋ := by
  let f : ∀ d : ℕ, 𝒢 d →+ B := fun d ↦
    { toFun := fun x ↦ (modelB d
        ((((q.hom (Int.ofNat d)).val.app (Opposite.op (U : S.Opens))).hom)
          ((modelA d).symm x))).val
      map_zero' := by simp
      map_add' := by intro x y; simp }
  exact
    { toRingHom := (DirectSum.toSemiring f (by
        change ((modelB 0)
          (((q.hom 0).val.app (Opposite.op (U : S.Opens))).hom
            ((modelA 0).symm (1 : 𝒢 0)))).val = (1 : B)
        have hA : (modelA 0).symm (1 : 𝒢 0) =
            𝒜.one (Opposite.op (U : S.Opens)) := by
          apply (modelA 0).injective
          simpa only [AddEquiv.apply_symm_apply] using (hModelA.one_eq).symm
        have hq := q.map_one (Opposite.op (U : S.Opens))
        have hB := hModelB.one_eq
        rw [hA]
        rw [hq]
        rw [hB]
        rfl) (by
        intro d e x y
        let qd := ((q.hom (Int.ofNat d)).val.app (Opposite.op (U : S.Opens))).hom
        let qe := ((q.hom (Int.ofNat e)).val.app (Opposite.op (U : S.Opens))).hom
        let qde := ((q.hom (Int.ofNat (d + e))).val.app (Opposite.op (U : S.Opens))).hom
        have hA := IsAffineOpenSectionModel.mul_eq 𝒢 𝒜 U modelA hModelA
          d e ((modelA d).symm x) ((modelA e).symm y)
        have hB := IsAffineOpenSectionModel.mul_eq ℋ ℬ U modelB hModelB d e
          (qd ((modelA d).symm x)) (qe ((modelA e).symm y))
        have hA' :
            𝒜.mul (Opposite.op (U : S.Opens)) (Int.ofNat d) (Int.ofNat e)
                ((modelA d).symm x) ((modelA e).symm y) =
              (modelA (d + e)).symm ((SetLike.gMul 𝒢).mul x y) := by
          simpa only [AddEquiv.apply_symm_apply] using (eq_of_heq hA)
        have hm : qde ((modelA (d + e)).symm ((SetLike.gMul 𝒢).mul x y)) =
            (modelB (d + e)).symm ((SetLike.gMul ℋ).mul
              (modelB d (qd ((modelA d).symm x)))
              (modelB e (qe ((modelA e).symm y)))) :=
          (congrArg qde hA'.symm).trans
            ((q.map_mul (Opposite.op (U : S.Opens))
              (Int.ofNat d) (Int.ofNat e) ((modelA d).symm x) ((modelA e).symm y)).trans
                (eq_of_heq hB))
        exact (congrArg (fun z ↦ (modelB (d + e) z).val) hm).trans
          (congrArg Subtype.val ((modelB (d + e)).apply_symm_apply _)))).comp
        (DirectSum.decomposeRingEquiv 𝒢).toRingHom
      map_mem := by
        intro d x hx
        change (DirectSum.toAddMonoid f) (DirectSum.decompose 𝒢 x) ∈ ℋ d
        rw [DirectSum.decompose_of_mem 𝒢 hx, DirectSum.toAddMonoid_of]
        exact (modelB d
          ((((q.hom (Int.ofNat d)).val.app (Opposite.op (U : S.Opens))).hom)
            ((modelA d).symm ⟨x, hx⟩))).property }

/-- On a homogeneous element, the transported map is exactly the corresponding sheaf map
on sections, expressed in the two affine models. -/
theorem mapOnSections_gradedAddHom (q : 𝒜 ⟶ ℬ) (d : ℕ) (x : 𝒢 d) :
    (mapOnSections U 𝒢 ℋ 𝒜 ℬ modelA modelB hModelA hModelB q).gradedAddHom d x =
      modelB d (((q.hom (Int.ofNat d)).val.app (Opposite.op (U : S.Opens))).hom
        ((modelA d).symm x)) := by
  apply Subtype.ext
  change (DirectSum.toAddMonoid _) (DirectSum.decompose 𝒢 x.val) = _
  rw [DirectSum.decompose_of_mem 𝒢 x.property, DirectSum.toAddMonoid_of]
  rfl

/-- Epimorphisms between quasi-coherent sheaves are surjective on affine sections, hence on
every homogeneous component of their genuine affine models. -/
theorem mapOnSections_surjective
    (hqcA : 𝒜.IsQuasicoherent) (hqcB : ℬ.IsQuasicoherent)
    (q : 𝒜 ⟶ ℬ) (hq : ∀ d : ℕ, Epi (q.hom (Int.ofNat d))) (d : ℕ) :
    Function.Surjective
      ((mapOnSections U 𝒢 ℋ 𝒜 ℬ modelA modelB hModelA hModelB q).gradedAddHom d) := by
  letI : (𝒜 (Int.ofNat d)).IsQuasicoherent := hqcA (Int.ofNat d)
  letI : (ℬ (Int.ofNat d)).IsQuasicoherent := hqcB (Int.ofNat d)
  -- Use the scheme-module category when applying the restriction functor.
  let f : (show S.Modules from 𝒜 (Int.ofNat d)) ⟶
      (show S.Modules from ℬ (Int.ofNat d)) := q.hom (Int.ofNat d)
  haveI : Epi f := hq d
  let R : CommRingCat := S.presheaf.obj (Opposite.op (U : S.Opens))
  let M := (Scheme.Modules.restrictFunctor U.property.fromSpec).obj (𝒜 (Int.ofNat d))
  let N := (Scheme.Modules.restrictFunctor U.property.fromSpec).obj (ℬ (Int.ofNat d))
  let g : M ⟶ N := (Scheme.Modules.restrictFunctor U.property.fromSpec).map f
  haveI hg : Epi g := inferInstanceAs
    (Epi ((Scheme.Modules.restrictFunctor U.property.fromSpec).map f))
  haveI hM : IsIso (Scheme.Modules.fromTildeΓ M) := inferInstance
  haveI hN : IsIso (Scheme.Modules.fromTildeΓ N) := inferInstance
  have hMepi : Epi (Scheme.Modules.fromTildeΓ M) := inferInstance
  haveI : Epi ((moduleSpecΓFunctor (R := R)).map g) := by
    -- The affine tilde counit is invertible and commutes with the restricted map.
    apply Functor.epi_of_epi_map (tilde.functor _)
    let t := (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map g)
    have he : t ≫ Scheme.Modules.fromTildeΓ N =
        Scheme.Modules.fromTildeΓ M ≫ g := (tilde.adjunction).counit.naturality g
    haveI : Epi (t ≫ Scheme.Modules.fromTildeΓ N) := by
      rw [he]
      exact epi_comp' hMepi hg
    exact (@epi_comp_iff_of_isIso _ _ _ _ _ t (Scheme.Modules.fromTildeΓ N) hN).mp
      inferInstance
  have hs := (ModuleCat.epi_iff_surjective
    ((moduleSpecΓFunctor (R := R)).map g)).mp inferInstance
  change Function.Surjective
    (((q.hom (Int.ofNat d)).val.app
      (Opposite.op (U.property.fromSpec ''ᵁ ⊤))).hom) at hs
  rw [U.property.fromSpec.image_top_eq_opensRange, U.property.opensRange_fromSpec] at hs
  intro y
  obtain ⟨x, hx⟩ := hs ((modelB d).symm y)
  refine ⟨modelA d x, ?_⟩
  rw [mapOnSections_gradedAddHom, AddEquiv.symm_apply_apply, hx,
    AddEquiv.apply_symm_apply]

/-- The full-domain projective-spectrum morphism induced by an epic graded sheaf map on
an affine open. This uses the canonical graded `Proj` map and its top-domain inclusion. -/
noncomputable def projMapOfEpi
    (hqcA : 𝒜.IsQuasicoherent) (hqcB : ℬ.IsQuasicoherent)
    (q : 𝒜 ⟶ ℬ) (hq : ∀ d : ℕ, Epi (q.hom (Int.ofNat d))) :
    Proj ℋ ⟶ Proj 𝒢 :=
  let φ := mapOnSections U 𝒢 ℋ 𝒜 ℬ modelA modelB hModelA hModelB q
  projMapOnTarget φ (projMapMap φ)
    (projMapDomain_eq_top_of_eventually_surjective ⟨0, fun d _ ↦
      mapOnSections_surjective U 𝒢 ℋ 𝒜 ℬ modelA modelB hModelA hModelB
        hqcA hqcB q hq d⟩)

end AlgebraicGeometry.AffineOpenSectionProj

namespace AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation

variable {S X Z : Scheme.{u}} {p : X ⟶ S}
variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
variable {A σ : S.affineOpens → Type u}
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
variable [∀ U, GradedRing (sectionGrading U)]
variable {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
variable {model : ∀ (U : S.affineOpens) (d : ℕ),
  (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d}

/-- The integral twist of a relative projective spectrum restricted to a subscheme. -/
noncomputable def closedSubschemeTwist
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) (d : ℤ) : Z.Modules :=
  (Scheme.Modules.pullback i).obj (presentation.twistAlgebra d)

/-- The pushforward to the base of a nonnegative twist restricted to a subscheme. -/
noncomputable def closedSubschemeDegreePiece
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) (d : ℕ) : S.Modules :=
  (Scheme.Modules.pushforward (i ≫ p)).obj
    (presentation.closedSubschemeTwist i (Int.ofNat d))

/-- The canonical degree map from a relative-projective graded algebra to the pushforward of
the corresponding twist restricted to a closed subscheme. -/
noncomputable def closedSubschemeDegreeMap
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) :
    𝒜 (Int.ofNat d) ⟶ presentation.closedSubschemeDegreePiece i d :=
  presentation.psi.hom d ≫
    (Scheme.Modules.pushforward p).map
      (Scheme.Modules.ClosedImmersion.restrictionMap i
        (presentation.twistAlgebra (Int.ofNat d))) ≫
    (Scheme.Modules.pushforwardComp i p).hom.app
      ((Scheme.Modules.pullback i).obj (presentation.twistAlgebra (Int.ofNat d)))

/-- The degreewise kernel of the canonical map to the pushed-forward restricted twist. -/
noncomputable def closedSubschemeDegreeKernel
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) : Subobject (𝒜 (Int.ofNat d)) :=
  kernelSubobject (presentation.closedSubschemeDegreeMap i d)

variable {sectionModel : ∀ (U : S.affineOpens) (d : ℕ),
  (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}

/-- A presentation of a closed subscheme as the relative projective spectrum of a quotient
graded algebra, including its affine models and the canonical quotient map. -/
structure ClosedSubschemeQuotient
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (sectionModel U d).toEquiv) p)
    (hqc : 𝒜.IsQuasicoherent)
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (sectionModel U))
    (i : Z ⟶ X) [IsClosedImmersion i] where
  /-- The quotient graded algebra on the base. -/
  algebra : GradedAlgebraSheaf.{u, u} S.sheaf
  /-- The quotient graded algebra is commutative. -/
  algebra_isCommutative : algebra.IsCommutative
  /-- Every degree of the quotient graded algebra is quasi-coherent. -/
  algebra_isQuasicoherent : algebra.IsQuasicoherent
  /-- The affine rings used to model the quotient relative projective spectrum. -/
  affineRing : S.affineOpens → Type u
  /-- The families of homogeneous pieces in the affine models. -/
  affineGrade : S.affineOpens → Type u
  /-- Each affine model carries a commutative-ring structure. -/
  [affineRingCommRing : ∀ U, CommRing (affineRing U)]
  /-- The homogeneous pieces are represented as subsets of the affine rings. -/
  [affineGradeSetLike : ∀ U, SetLike (affineGrade U) (affineRing U)]
  /-- The homogeneous pieces are additive subgroups of the affine rings. -/
  [affineGradeAddSubgroupClass :
    ∀ U, AddSubgroupClass (affineGrade U) (affineRing U)]
  /-- The nonnegative grading on each affine model. -/
  affineGrading : ∀ U : S.affineOpens, ℕ → affineGrade U
  /-- The affine gradings are multiplicative and decompose their rings. -/
  [affineGradedRing : ∀ U, GradedRing (affineGrading U)]
  /-- The projective-spectrum twist presentation on each affine model. -/
  affinePresentation :
    ∀ U : S.affineOpens, ProjTwistPresentation (affineGrading U)
  /-- The quotient algebra's degree pieces agree with the affine homogeneous pieces. -/
  affineModel : ∀ (U : S.affineOpens) (d : ℕ),
    (algebra (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ affineGrading U d
  /-- The affine models preserve the graded unit and homogeneous multiplication. -/
  affineModel_spec : ∀ U : S.affineOpens,
    AffineOpenSectionProj.IsAffineOpenSectionModel
      (affineGrading U) algebra U (affineModel U)
  /-- The rich relative-projective twist presentation of the closed subscheme. -/
  quotientPresentation : RelativeProjTwist.Presentation algebra affineRing affineGrade
    affineGrading affinePresentation (fun U d ↦ (affineModel U d).toEquiv) (i ≫ p)
  /-- The homomorphism from the original algebra to the quotient algebra. -/
  quotientMap : 𝒜 ⟶ algebra
  /-- The quotient homomorphism is degreewise epic in nonnegative degrees. -/
  quotientMap_epi : ∀ d : ℕ, Epi (quotientMap.hom (Int.ofNat d))
  /-- In the chosen affine charts, the actual quotient-induced Proj morphism is the specified
  closed immersion. Thus the quotient represents a closed subscheme of `X`, not just an
  isomorphic scheme over `S`. -/
  embedding_commutes : ∀ U : S.affineOpens,
    (quotientPresentation.localSchemeIso U).hom ≫
        AffineOpenSectionProj.projMapOfEpi U (sectionGrading U) (affineGrading U)
          𝒜 algebra (sectionModel U) (affineModel U) (hModel U) (affineModel_spec U)
          hqc algebra_isQuasicoherent quotientMap quotientMap_epi ≫
        (presentation.localSchemeIso U).inv ≫ (p ⁻¹ᵁ (U : S.Opens)).ι =
      ((i ≫ p) ⁻¹ᵁ (U : S.Opens)).ι ≫ i

namespace ClosedSubschemeQuotient

/-- Construct a closed-subscheme quotient presentation from its algebra, affine models,
relative-projective presentation, quotient map, and defining properties. -/
def ofComponents
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (sectionModel U d).toEquiv) p)
    (hqc : 𝒜.IsQuasicoherent)
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (sectionModel U))
    (i : Z ⟶ X) [IsClosedImmersion i]
    (algebra : GradedAlgebraSheaf.{u, u} S.sheaf)
    (algebra_isCommutative : algebra.IsCommutative)
    (algebra_isQuasicoherent : algebra.IsQuasicoherent)
    (affineRing affineGrade : S.affineOpens → Type u)
    [affineRingCommRing : ∀ U, CommRing (affineRing U)]
    [affineGradeSetLike : ∀ U, SetLike (affineGrade U) (affineRing U)]
    [affineGradeAddSubgroupClass :
      ∀ U, AddSubgroupClass (affineGrade U) (affineRing U)]
    (affineGrading : ∀ U : S.affineOpens, ℕ → affineGrade U)
    [affineGradedRing : ∀ U, GradedRing (affineGrading U)]
    (affinePresentation :
      ∀ U : S.affineOpens, ProjTwistPresentation (affineGrading U))
    (affineModel : ∀ (U : S.affineOpens) (d : ℕ),
      (algebra (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ affineGrading U d)
    (affineModel_spec : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (affineGrading U) algebra U (affineModel U))
    (quotientPresentation : RelativeProjTwist.Presentation algebra affineRing affineGrade
      affineGrading affinePresentation (fun U d ↦ (affineModel U d).toEquiv) (i ≫ p))
    (quotientMap : 𝒜 ⟶ algebra)
    (quotientMap_epi : ∀ d : ℕ, Epi (quotientMap.hom (Int.ofNat d)))
    (embedding_commutes : ∀ U : S.affineOpens,
      (quotientPresentation.localSchemeIso U).hom ≫
          AffineOpenSectionProj.projMapOfEpi U (sectionGrading U) (affineGrading U)
            𝒜 algebra (sectionModel U) (affineModel U) (hModel U) (affineModel_spec U)
            hqc algebra_isQuasicoherent quotientMap quotientMap_epi ≫
          (presentation.localSchemeIso U).inv ≫ (p ⁻¹ᵁ (U : S.Opens)).ι =
        ((i ≫ p) ⁻¹ᵁ (U : S.Opens)).ι ≫ i) :
    ClosedSubschemeQuotient presentation hqc hModel i where
  algebra := algebra
  algebra_isCommutative := algebra_isCommutative
  algebra_isQuasicoherent := algebra_isQuasicoherent
  affineRing := affineRing
  affineGrade := affineGrade
  affineRingCommRing := affineRingCommRing
  affineGradeSetLike := affineGradeSetLike
  affineGradeAddSubgroupClass := affineGradeAddSubgroupClass
  affineGrading := affineGrading
  affineGradedRing := affineGradedRing
  affinePresentation := affinePresentation
  affineModel := affineModel
  affineModel_spec := affineModel_spec
  quotientPresentation := quotientPresentation
  quotientMap := quotientMap
  quotientMap_epi := quotientMap_epi
  embedding_commutes := embedding_commutes

attribute [local instance]
  ClosedSubschemeQuotient.affineRingCommRing
  ClosedSubschemeQuotient.affineGradeSetLike
  ClosedSubschemeQuotient.affineGradeAddSubgroupClass
  ClosedSubschemeQuotient.affineGradedRing

/-- The morphism to the ambient scheme induced by the quotient on an affine base chart.
Its scheme map is computed from the sheaf map on genuine homogeneous sections. -/
noncomputable def affineMap
    {presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (sectionModel U d).toEquiv) p}
    {hqc : 𝒜.IsQuasicoherent}
    {hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (sectionModel U)}
    {i : Z ⟶ X} [IsClosedImmersion i]
    (Q : ClosedSubschemeQuotient presentation hqc hModel i) (U : S.affineOpens) :
    ((i ≫ p) ⁻¹ᵁ (U : S.Opens)).toScheme ⟶ X :=
  (Q.quotientPresentation.localSchemeIso U).hom ≫
    AffineOpenSectionProj.projMapOfEpi U (sectionGrading U) (Q.affineGrading U)
      𝒜 Q.algebra (sectionModel U) (Q.affineModel U) (hModel U) (Q.affineModel_spec U)
      hqc Q.algebra_isQuasicoherent Q.quotientMap Q.quotientMap_epi ≫
    (presentation.localSchemeIso U).inv ≫ (p ⁻¹ᵁ (U : S.Opens)).ι

/-- The quotient-induced morphism agrees with the specified closed immersion on every
affine chart of the base. -/
theorem affineMap_eq
    {presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (sectionModel U d).toEquiv) p}
    {hqc : 𝒜.IsQuasicoherent}
    {hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (sectionModel U)}
    {i : Z ⟶ X} [IsClosedImmersion i]
    (Q : ClosedSubschemeQuotient presentation hqc hModel i) (U : S.affineOpens) :
    Q.affineMap U = ((i ≫ p) ⁻¹ᵁ (U : S.Opens)).ι ≫ i :=
  Q.embedding_commutes U

/-- The defining commutativity, quasi-coherence, and epimorphy properties of a closed-subscheme
quotient presentation. -/
theorem spec
    {presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (sectionModel U d).toEquiv) p}
    {hqc : 𝒜.IsQuasicoherent}
    {hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (sectionModel U)}
    {i : Z ⟶ X} [IsClosedImmersion i]
    (Q : ClosedSubschemeQuotient presentation hqc hModel i) :
    Q.algebra.IsCommutative ∧
      Q.algebra.IsQuasicoherent ∧
        ∀ d : ℕ, Epi (Q.quotientMap.hom (Int.ofNat d)) := by
  exact ⟨Q.algebra_isCommutative, Q.algebra_isQuasicoherent, Q.quotientMap_epi⟩

/-- A closed-subscheme quotient is generated by a subobject in degree `d` when the quotient map
kills that subobject and is universal among graded-algebra maps that kill it. -/
def IsQuotientByDegreeSubobject
    {presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (sectionModel U d).toEquiv) p}
    {hqc : 𝒜.IsQuasicoherent}
    {hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (sectionModel U)}
    {i : Z ⟶ X} [IsClosedImmersion i]
    (Q : ClosedSubschemeQuotient presentation hqc hModel i) (d : ℕ)
    (F : Subobject (𝒜 (Int.ofNat d))) : Prop :=
  F.arrow ≫ Q.quotientMap.hom (Int.ofNat d) = 0 ∧
    ∀ (ℬ : GradedAlgebraSheaf.{u, u} S.sheaf) (g : 𝒜 ⟶ ℬ),
      F.arrow ≫ g.hom (Int.ofNat d) = 0 ↔
        ∃! h : Q.algebra ⟶ ℬ, Q.quotientMap ≫ h = g

end ClosedSubschemeQuotient

/-- A canonical quotient presentation whose degreewise kernels are the kernels of the maps to
the pushed-forward twists restricted to the closed subscheme. -/
structure CanonicalClosedSubschemeQuotient
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (sectionModel U d).toEquiv) p)
    (hqc : 𝒜.IsQuasicoherent)
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (sectionModel U))
    (i : Z ⟶ X) [IsClosedImmersion i]
    extends ClosedSubschemeQuotient presentation hqc hModel i where
  /-- The kernel in every nonnegative degree is the canonical restricted-twist kernel. -/
  quotientMap_kernel : ∀ d : ℕ,
    kernelSubobject (quotientMap.hom (Int.ofNat d)) =
      presentation.closedSubschemeDegreeKernel i d

namespace CanonicalClosedSubschemeQuotient

/-- Equip a quotient presentation with its degreewise canonical-kernel identification. -/
def ofQuotient
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (sectionModel U d).toEquiv) p)
    (hqc : 𝒜.IsQuasicoherent)
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (sectionModel U))
    (i : Z ⟶ X) [IsClosedImmersion i]
    (quotient : ClosedSubschemeQuotient presentation hqc hModel i)
    (quotientMap_kernel : ∀ d : ℕ,
      kernelSubobject (quotient.quotientMap.hom (Int.ofNat d)) =
        presentation.closedSubschemeDegreeKernel i d) :
    CanonicalClosedSubschemeQuotient presentation hqc hModel i where
  toClosedSubschemeQuotient := quotient
  quotientMap_kernel := quotientMap_kernel

/-- The defining commutativity, quasi-coherence, epimorphy, and kernel properties of a canonical
closed-subscheme quotient presentation. -/
theorem spec
    {presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (sectionModel U d).toEquiv) p}
    {hqc : 𝒜.IsQuasicoherent}
    {hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (sectionModel U)}
    {i : Z ⟶ X} [IsClosedImmersion i]
    (Q : CanonicalClosedSubschemeQuotient presentation hqc hModel i) :
    Q.algebra.IsCommutative ∧
      Q.algebra.IsQuasicoherent ∧
        (∀ d : ℕ, Epi (Q.quotientMap.hom (Int.ofNat d))) ∧
          ∀ d : ℕ, kernelSubobject (Q.quotientMap.hom (Int.ofNat d)) =
            presentation.closedSubschemeDegreeKernel i d := by
  exact ⟨Q.algebra_isCommutative, Q.algebra_isQuasicoherent,
    Q.quotientMap_epi, Q.quotientMap_kernel⟩

end CanonicalClosedSubschemeQuotient

/-- A closed subscheme of a quasi-compact relative projective spectrum has a relative-projective
presentation by the quotient of the source graded algebra by the kernels of the canonical maps
to its pushed-forward restricted twists. -/
theorem existsClosedSubschemeQuotientPresentation
    (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
    (hqc : 𝒜.IsQuasicoherent)
    (A σ : S.affineOpens → Type u)
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    (model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d)
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel (sectionGrading U) 𝒜 U (model U))
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact p] :
    Nonempty (presentation.CanonicalClosedSubschemeQuotient hqc hModel i) := sorry

/-- Over a quasi-compact quasi-separated base, every finitely presented closed subscheme of a
quasi-compact relative projective spectrum is cut out by a finite-type quasi-coherent subobject
in one positive degree. -/
theorem existsQuotientByFiniteTypeDegreeSubobject
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
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d)
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel (sectionGrading U) 𝒜 U (model U))
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) p)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact p]
    [Scheme.Hom.FinitePresentation i] :
    ∃ (d : ℕ) (F : Subobject (𝒜 (Int.ofNat d)))
      (Q : presentation.ClosedSubschemeQuotient hqc hModel i),
      0 < d ∧
        F ∈ Scheme.Modules.finiteTypeQuasiCoherentSubobjects (𝒜 (Int.ofNat d)) ∧
          Q.IsQuotientByDegreeSubobject d F := sorry

end AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation
