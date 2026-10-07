module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Characterization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.SectionRingProj.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Separated

/-!
# Canonical relative projective comparison

This module bundles a chosen full-source canonical comparison from a scheme carrying a
relatively ample module to the relative projective spectrum of its pushed-forward tensor powers.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A chosen canonical full-source comparison from a scheme with a relatively ample module to
the relative projective spectrum of the pushforwards of its nonnegative tensor powers. -/
structure CanonicalRelativeProjComparison
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [RelativelyAmple f L] where
  /-- The invertibility data used to form all integral powers of the module. -/
  [invertible : Scheme.Modules.Invertible L]
  /-- The graded algebra sheaf defining the chosen relative projective spectrum. -/
  algebra : GradedAlgebraSheaf.{u, u} S.sheaf
  /-- The defining graded algebra is commutative. -/
  [algebraComm : algebra.IsCommutative]
  /-- Every homogeneous piece of the defining algebra is quasi-coherent. -/
  algebraQuasicoherent : algebra.IsQuasicoherent
  /-- The affine section rings used to realize the relative projective spectrum. -/
  sectionRing : S.affineOpens → Type u
  /-- The affine section models are commutative rings. -/
  [sectionRingComm : ∀ U, CommRing (sectionRing U)]
  /-- The types containing the homogeneous pieces of the affine section models. -/
  homogeneousCarrier : S.affineOpens → Type u
  /-- Each homogeneous carrier is realized inside its affine section ring. -/
  [homogeneousCarrierSetLike :
    ∀ U, SetLike (homogeneousCarrier U) (sectionRing U)]
  /-- Each homogeneous carrier is closed under the additive operations. -/
  [homogeneousCarrierAddSubgroup :
    ∀ U, AddSubgroupClass (homogeneousCarrier U) (sectionRing U)]
  /-- The nonnegative grading on each affine section model. -/
  sectionGrading : ∀ U : S.affineOpens, ℕ → homogeneousCarrier U
  /-- Each affine section model carries the prescribed graded-ring structure. -/
  [sectionGradingRing : ∀ U, GradedRing (sectionGrading U)]
  /-- The degreewise identifications between sheaf sections and the affine graded models. -/
  model : ∀ (U : S.affineOpens) (d : ℕ),
    (algebra (Int.ofNat d)).val.obj (op (U : S.Opens)) ≃+ sectionGrading U d
  /-- The affine identifications preserve the unit and homogeneous multiplication. -/
  model_spec : ∀ U : S.affineOpens,
    AffineOpenSectionProj.IsAffineOpenSectionModel
      (sectionGrading U) algebra U (model U)
  /-- The twist presentation chosen on every affine graded model. -/
  twistPresentation : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)
  /-- Restriction of homogeneous affine sections along inclusions of affine opens. -/
  sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
    (U : S.Opens) ≤ (U' : S.Opens) →
      sectionGrading U' →+*ᵍ sectionGrading U
  /-- The affine models intertwine sheaf restriction with graded-ring restriction. -/
  sectionRestrict_spec :
    ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
      (d : ℕ) (x : sectionGrading U' d),
      model U d
          ((((algebra (Int.ofNat d)).val.map (homOfLE h).op).hom)
            ((model U' d).symm x)) =
        (sectionRestrict h).gradedAddHom d x
  /-- The equipped relative projective spectrum obtained from the affine models. -/
  realization : Scheme.RelativeProjRealization algebra algebraQuasicoherent
    sectionRing homogeneousCarrier sectionGrading model model_spec twistPresentation
    sectionRestrict sectionRestrict_spec
  /-- The compatible global presentation of the relative twists. -/
  presentation : Scheme.RelativeProjTwist.Presentation algebra sectionRing homogeneousCarrier
    sectionGrading twistPresentation (fun U d ↦ (model U d).toEquiv)
    (Scheme.relativeProjπ realization)
  /-- The multiplicative map from the defining algebra to the pushed-forward integral powers. -/
  sectionHom : Scheme.RelativeProjTwist.Hom algebra f
    (@RingedSpace.InvertiblePower.gradedAlgebra _ L
      (Scheme.Modules.Invertible.ringedSpaceIsInvertible invertible))
  /-- The relative projective functor represented by the chosen realization. -/
  relativeProjFunctor : RelativeProjFunctor S algebra
  /-- The positive-degree charts of the functor are associated to the canonical quadruples. -/
  associatedToQuadruples : ∀ d : {n : ℕ // 1 ≤ n},
    (relativeProjFunctor.degreeFunctor d).IsAssociatedToQuadruples
  /-- The functor point represented by the chosen relative projective realization. -/
  representedPoint : relativeProjFunctor.toFunctor.obj
    (op (Scheme.relativeProj realization))
  /-- The canonical relative projective section map on its natural open domain. -/
  sectionMap : Scheme.Modules.RelativeProjSectionMap algebra algebraQuasicoherent
    sectionRing homogeneousCarrier sectionGrading model model_spec twistPresentation
    sectionRestrict sectionRestrict_spec realization presentation f L sectionHom
  /-- The section map agrees globally and affine-locally with the canonical constructions. -/
  sectionMap_isCanonical : Scheme.Modules.RelativeProjSectionMap.IsCanonical
    (𝒜 := algebra) (F := relativeProjFunctor)
    (associatedToQuadruples := associatedToQuadruples)
    (representedPoint := representedPoint) (c := sectionMap)
  /-- The canonical section map is defined on the whole source scheme. -/
  domain_eq_top : sectionMap.domain = ⊤
  /-- The morphism induced on the full source by the canonical section map. -/
  comparisonMap : X ⟶ realization.Y
  /-- The full-source comparison is obtained from the top-domain identification and the
  canonical section map. -/
  comparisonMap_eq : comparisonMap =
    (Scheme.topIso X).inv ≫ (X.isoOfEq domain_eq_top.symm).hom ≫ sectionMap.map
  /-- In every nonnegative degree the defining algebra is the pushforward of the corresponding
  tensor power. -/
  algebra_eq_pushforward : ∀ d : ℕ,
    algebra (Int.ofNat d) =
      (Scheme.Modules.pushforward f).obj (RingedSpace.TensorPower.sheaf L d)
  /-- The multiplicative section homomorphism is the canonical pushforward map in every
  nonnegative degree. -/
  sectionHom_eq_pushforward : ∀ d : ℕ,
    sectionHom.hom d =
      eqToHom (algebra_eq_pushforward d) ≫
        (Scheme.Modules.pushforward f).map
          (@RingedSpace.InvertiblePower.natIso _ L
            (Scheme.Modules.Invertible.ringedSpaceIsInvertible invertible) d).hom
  /-- The induced full-source comparison is an open immersion. -/
  comparison_isOpenImmersion : IsOpenImmersion comparisonMap

namespace CanonicalRelativeProjComparison

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules} [RelativelyAmple f L]

/-- Construct a canonical full-source relative projective comparison from explicit affine
models, realization data, and a canonical section map. -/
def ofSectionMap
    [invertible : Scheme.Modules.Invertible L]
    (algebra : GradedAlgebraSheaf.{u, u} S.sheaf) [algebraComm : algebra.IsCommutative]
    (algebraQuasicoherent : algebra.IsQuasicoherent)
    (sectionRing homogeneousCarrier : S.affineOpens → Type u)
    [sectionRingComm : ∀ U, CommRing (sectionRing U)]
    [homogeneousCarrierSetLike : ∀ U, SetLike (homogeneousCarrier U) (sectionRing U)]
    [homogeneousCarrierAddSubgroup :
      ∀ U, AddSubgroupClass (homogeneousCarrier U) (sectionRing U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → homogeneousCarrier U)
    [sectionGradingRing : ∀ U, GradedRing (sectionGrading U)]
    (model : ∀ (U : S.affineOpens) (d : ℕ),
      (algebra (Int.ofNat d)).val.obj (op (U : S.Opens)) ≃+ sectionGrading U d)
    (model_spec : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) algebra U (model U))
    (twistPresentation : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
      (U : S.Opens) ≤ (U' : S.Opens) →
        sectionGrading U' →+*ᵍ sectionGrading U)
    (sectionRestrict_spec :
      ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
        (d : ℕ) (x : sectionGrading U' d),
        model U d
            ((((algebra (Int.ofNat d)).val.map (homOfLE h).op).hom)
              ((model U' d).symm x)) =
          (sectionRestrict h).gradedAddHom d x)
    (realization : Scheme.RelativeProjRealization algebra algebraQuasicoherent
      sectionRing homogeneousCarrier sectionGrading model model_spec twistPresentation
      sectionRestrict sectionRestrict_spec)
    (presentation : Scheme.RelativeProjTwist.Presentation algebra sectionRing
      homogeneousCarrier sectionGrading twistPresentation
      (fun U d ↦ (model U d).toEquiv) (Scheme.relativeProjπ realization))
    (sectionHom : Scheme.RelativeProjTwist.Hom algebra f
      (@RingedSpace.InvertiblePower.gradedAlgebra _ L
        (Scheme.Modules.Invertible.ringedSpaceIsInvertible invertible)))
    (relativeProjFunctor : RelativeProjFunctor S algebra)
    (associatedToQuadruples : ∀ d : {n : ℕ // 1 ≤ n},
      (relativeProjFunctor.degreeFunctor d).IsAssociatedToQuadruples)
    (representedPoint : relativeProjFunctor.toFunctor.obj
      (op (Scheme.relativeProj realization)))
    (sectionMap : Scheme.Modules.RelativeProjSectionMap algebra algebraQuasicoherent
      sectionRing homogeneousCarrier sectionGrading model model_spec twistPresentation
      sectionRestrict sectionRestrict_spec realization presentation f L sectionHom)
    (sectionMap_isCanonical : Scheme.Modules.RelativeProjSectionMap.IsCanonical
      (𝒜 := algebra) (F := relativeProjFunctor)
      (associatedToQuadruples := associatedToQuadruples)
      (representedPoint := representedPoint) (c := sectionMap))
    (domain_eq_top : sectionMap.domain = ⊤)
    (algebra_eq_pushforward : ∀ d : ℕ,
      algebra (Int.ofNat d) =
        (Scheme.Modules.pushforward f).obj (RingedSpace.TensorPower.sheaf L d))
    (sectionHom_eq_pushforward : ∀ d : ℕ,
      sectionHom.hom d =
        eqToHom (algebra_eq_pushforward d) ≫
          (Scheme.Modules.pushforward f).map
            (@RingedSpace.InvertiblePower.natIso _ L
              (Scheme.Modules.Invertible.ringedSpaceIsInvertible invertible) d).hom)
    (comparison_isOpenImmersion : IsOpenImmersion
      ((Scheme.topIso X).inv ≫ (X.isoOfEq domain_eq_top.symm).hom ≫ sectionMap.map)) :
    CanonicalRelativeProjComparison f L where
  invertible := invertible
  algebra := algebra
  algebraComm := algebraComm
  algebraQuasicoherent := algebraQuasicoherent
  sectionRing := sectionRing
  sectionRingComm := sectionRingComm
  homogeneousCarrier := homogeneousCarrier
  homogeneousCarrierSetLike := homogeneousCarrierSetLike
  homogeneousCarrierAddSubgroup := homogeneousCarrierAddSubgroup
  sectionGrading := sectionGrading
  sectionGradingRing := sectionGradingRing
  model := model
  model_spec := model_spec
  twistPresentation := twistPresentation
  sectionRestrict := sectionRestrict
  sectionRestrict_spec := sectionRestrict_spec
  realization := realization
  presentation := presentation
  sectionHom := sectionHom
  relativeProjFunctor := relativeProjFunctor
  associatedToQuadruples := associatedToQuadruples
  representedPoint := representedPoint
  sectionMap := sectionMap
  sectionMap_isCanonical := sectionMap_isCanonical
  domain_eq_top := domain_eq_top
  comparisonMap :=
    (Scheme.topIso X).inv ≫ (X.isoOfEq domain_eq_top.symm).hom ≫ sectionMap.map
  comparisonMap_eq := rfl
  algebra_eq_pushforward := algebra_eq_pushforward
  sectionHom_eq_pushforward := sectionHom_eq_pushforward
  comparison_isOpenImmersion := comparison_isOpenImmersion

/-- The two canonical pushforward conditions satisfied by the defining algebra and its
multiplicative section homomorphism. -/
theorem canonical_spec (P : CanonicalRelativeProjComparison f L) :
    (∀ d : ℕ,
      P.algebra (Int.ofNat d) =
        (Scheme.Modules.pushforward f).obj (RingedSpace.TensorPower.sheaf L d)) ∧
      ∀ d : ℕ,
        P.sectionHom.hom d =
          eqToHom (P.algebra_eq_pushforward d) ≫
            (Scheme.Modules.pushforward f).map
              (@RingedSpace.InvertiblePower.natIso _ L
                (Scheme.Modules.Invertible.ringedSpaceIsInvertible P.invertible) d).hom := sorry

/-- The adjoint degreewise map from the pulled-back defining algebra to the tensor powers of
the relatively ample module. -/
noncomputable def psi (P : CanonicalRelativeProjComparison f L) (d : ℕ) :
    (Scheme.Modules.pullback f).obj (P.algebra (Int.ofNat d)) ⟶
      RingedSpace.TensorPower.sheaf L d :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      (P.algebra (Int.ofNat d)) (RingedSpace.TensorPower.sheaf L d)).symm
    (P.sectionHom.hom d ≫
      (Scheme.Modules.pushforward f).map
        (@RingedSpace.InvertiblePower.natIso _ L
          (Scheme.Modules.Invertible.ringedSpaceIsInvertible P.invertible) d).inv)

/-- The adjoint degreewise map is pullback of the canonical pushforward identification followed
by the counit of the pullback-pushforward adjunction. -/
theorem psi_eq_adjunction (P : CanonicalRelativeProjComparison f L) (d : ℕ) :
    P.psi d =
      (Scheme.Modules.pullback f).map (eqToHom (P.algebra_eq_pushforward d)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app
          (RingedSpace.TensorPower.sheaf L d) := sorry

/-- The canonical morphism from the full source to the chosen relative projective spectrum. -/
def comparison (P : CanonicalRelativeProjComparison f L) :
    X ⟶ @Scheme.relativeProj S P.algebra P.algebraComm P.algebraQuasicoherent
      P.sectionRing P.homogeneousCarrier P.sectionRingComm
      P.homogeneousCarrierSetLike P.homogeneousCarrierAddSubgroup
      P.sectionGrading P.sectionGradingRing P.model P.model_spec
      P.twistPresentation P.sectionRestrict P.sectionRestrict_spec P.realization :=
  P.comparisonMap

/-- The canonical comparison commutes with the structural morphisms to the base. -/
theorem overBase (P : CanonicalRelativeProjComparison f L) :
    P.comparison ≫
      @Scheme.relativeProjπ S P.algebra P.algebraComm P.algebraQuasicoherent
        P.sectionRing P.homogeneousCarrier P.sectionRingComm
        P.homogeneousCarrierSetLike P.homogeneousCarrierAddSubgroup
        P.sectionGrading P.sectionGradingRing P.model P.model_spec
        P.twistPresentation P.sectionRestrict P.sectionRestrict_spec P.realization = f := sorry

/-- The canonical relative projective comparison has dense image. -/
theorem isDominant (P : CanonicalRelativeProjComparison f L) :
    IsDominant P.comparison := sorry

/-- A canonical relative projective comparison over a universally closed morphism is an
isomorphism. -/
theorem isIso [UniversallyClosed f] (P : CanonicalRelativeProjComparison f L) :
    IsIso P.comparison := sorry

/-- A scheme proper over an affine base with an ample invertible module admits a canonical
relative projective comparison that is an isomorphism. -/
theorem exists_isIso_of_isProperOverSpec
    {R : Type u} [CommRing R] {P : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L : P.Modules) [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L] :
    ∃ C : CanonicalRelativeProjComparison p L, IsIso C.comparison := sorry

end CanonicalRelativeProjComparison

end AlgebraicGeometry
