/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ProjFromSections
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.TwistComparison

/-!
# Morphisms to relative projective spectra from sections

A multiplicative map from a graded algebra sheaf to the integral powers of an invertible
module determines an open-domain morphism to relative projective spectrum.  This module records
the complete comparison datum and its affine and fixed-degree characterizations.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {S : Scheme.{u}}
variable (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
variable (hqc : 𝒜.IsQuasicoherent)
variable (A σ : S.affineOpens → Type u)
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
variable [∀ U, GradedRing (sectionGrading U)]
variable (model : ∀ (U : S.affineOpens) (d : ℕ),
  (𝒜 (Int.ofNat d)).val.obj (op (U : S.Opens)) ≃+ sectionGrading U d)
variable (hModel : ∀ U : S.affineOpens,
  AffineOpenSectionProj.IsAffineOpenSectionModel (sectionGrading U) 𝒜 U (model U))
variable (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
variable (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
  (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
variable (sectionRestrict_spec :
  ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
    (d : ℕ) (x : sectionGrading U' d),
    model U d
        ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom) ((model U' d).symm x)) =
      (sectionRestrict h).gradedAddHom d x)
variable (R : Scheme.RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
  sectionRestrict sectionRestrict_spec)
variable (presentation : Scheme.RelativeProjTwist.Presentation 𝒜 A σ sectionGrading P
  (fun U d ↦ (model U d).toEquiv) (Scheme.relativeProjπ R))
variable {T : Scheme.{u}} (f : T ⟶ S) (L : T.Modules) [Invertible L]
variable (ψ : Scheme.RelativeProjTwist.Hom 𝒜 f
  (@RingedSpace.InvertiblePower.gradedAlgebra _ L
    (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L))))

/-- An open subscheme, its morphism to a relative projective spectrum over the base, and the
multiplicative comparison from pulled-back relative twists to the restricted integral powers
of an invertible module. -/
structure RelativeProjSectionMap
    (ψ : Scheme.RelativeProjTwist.Hom 𝒜 f
      (@RingedSpace.InvertiblePower.gradedAlgebra _ L
        (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L)))) where
  /-- The open on which the relative projective morphism is defined. -/
  domain : T.Opens
  /-- The morphism from the open domain to the chosen relative projective realization. -/
  map : domain.toScheme ⟶ Scheme.relativeProj R
  /-- The morphism commutes with the structure maps to the base scheme. -/
  map_over_base : map ≫ Scheme.relativeProjπ R = domain.ι ≫ f
  /-- The multiplicative comparison from relative twists to the restricted powers of `L`. -/
  theta : Scheme.RelativeProjTwist.Hom presentation.twistAlgebra map
    (pullbackInvertiblePowerGradedAlgebra domain.ι L)

namespace RelativeProjSectionMap

/-- Construct a relative projective section map from its open, morphism, over-base equality,
and multiplicative twist comparison. -/
def of
    (domain : T.Opens) (map : domain.toScheme ⟶ Scheme.relativeProj R)
    (map_over_base : map ≫ Scheme.relativeProjπ R = domain.ι ≫ f)
    (theta : Scheme.RelativeProjTwist.Hom presentation.twistAlgebra map
      (pullbackInvertiblePowerGradedAlgebra domain.ι L)) :
    RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ where
  domain := domain
  map := map
  map_over_base := map_over_base
  theta := theta

/-- The map obtained by restricting a relative projective section map over an affine open of
the base and identifying that chart with its absolute projective spectrum. -/
noncomputable def affineRestrictionMap
    (c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ)
    (U : S.affineOpens) :
    (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).toScheme ⟶
      Proj (sectionGrading U) :=
  Scheme.Hom.resLE c.map (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))
      (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))) le_rfl ≫
    (R.localIso U).hom

/-- Compatibility of a twist comparison with the original graded map, expressed after
pushforward to the base in every nonnegative degree. -/
def ThetaCompatible
    (c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ) : Prop :=
  ∀ n : ℕ,
    presentation.psi.hom n ≫
          (Scheme.Modules.pushforward (Scheme.relativeProjπ R)).map (c.theta.hom n) ≫
          (Scheme.Modules.pushforwardComp c.map (Scheme.relativeProjπ R)).hom.app
            (pullbackInvertiblePowerGradedAlgebra c.domain.ι L (Int.ofNat n)) ≫
          (Scheme.Modules.pushforwardCongr c.map_over_base).hom.app
            (pullbackInvertiblePowerGradedAlgebra c.domain.ι L (Int.ofNat n)) =
      ψ.hom n ≫
          (Scheme.Modules.pushforward f).map
            ((Scheme.Modules.pullbackPushforwardAdjunction c.domain.ι).unit.app
              (@RingedSpace.InvertiblePower.sheaf _ L
                (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L))
                (Int.ofNat n))) ≫
          (Scheme.Modules.pushforwardComp c.domain.ι f).hom.app
            ((Scheme.Modules.pullback c.domain.ι).obj
              (@RingedSpace.InvertiblePower.sheaf _ L
                (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L))
                (Int.ofNat n)))

/-- Pushforward compatibility is equivalent to the complete family of degreewise commutative
squares defining a compatible twist comparison. -/
theorem thetaCompatible_spec
    (c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ) :
    ThetaCompatible (𝒜 := 𝒜) (presentation := presentation) (f := f) (L := L)
      (ψ := ψ) (c := c) ↔
      ∀ n : ℕ,
        presentation.psi.hom n ≫
              (Scheme.Modules.pushforward (Scheme.relativeProjπ R)).map (c.theta.hom n) ≫
              (Scheme.Modules.pushforwardComp c.map (Scheme.relativeProjπ R)).hom.app
                (pullbackInvertiblePowerGradedAlgebra c.domain.ι L (Int.ofNat n)) ≫
              (Scheme.Modules.pushforwardCongr c.map_over_base).hom.app
                (pullbackInvertiblePowerGradedAlgebra c.domain.ι L (Int.ofNat n)) =
          ψ.hom n ≫
              (Scheme.Modules.pushforward f).map
                ((Scheme.Modules.pullbackPushforwardAdjunction c.domain.ι).unit.app
                  (@RingedSpace.InvertiblePower.sheaf _ L
                    (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L))
                    (Int.ofNat n))) ≫
              (Scheme.Modules.pushforwardComp c.domain.ι f).hom.app
                ((Scheme.Modules.pullback c.domain.ι).obj
                  (@RingedSpace.InvertiblePower.sheaf _ L
                    (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L))
                    (Int.ofNat n))) := sorry

/-- The degreewise map obtained by restricting the original multiplicative map to an open and
transporting from degree `n * d` to the `n`th power of the restricted degree-`d` line bundle. -/
noncomputable def restrictedDegreeHom
    (W : T.Opens) (d n : ℕ) :
    𝒜 (Int.ofNat (n * d)) ⟶
      (Scheme.Modules.pushforward (W.ι ≫ f)).obj
        (RingedSpace.TensorPower.sheaf (restrictedVeroneseLineBundle L W d) n) :=
  ψ.hom (n * d) ≫
    (Scheme.Modules.pushforward f).map
      (@RingedSpace.InvertiblePower.natIso _ L
        (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L)) (n * d)).inv ≫
    (Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app
        (RingedSpace.TensorPower.sheaf L (n * d))) ≫
    (Scheme.Modules.pushforwardComp W.ι f).hom.app
      ((Scheme.Modules.pullback W.ι).obj (RingedSpace.TensorPower.sheaf L (n * d))) ≫
    (Scheme.Modules.pushforward (W.ι ≫ f)).map
      (restrictedVeronesePowerIso L W d n).inv

/-- The adjoint degree-one map of the canonical degree-`d` restriction of the original graded
map to an open subscheme. -/
noncomputable def restrictedDegreeMap
    (W : T.Opens) (d : ℕ) :
    (Scheme.Modules.pullback (W.ι ≫ f)).obj (𝒜 (Int.ofNat (1 * d))) ⟶
      RingedSpace.TensorPower.sheaf (restrictedVeroneseLineBundle L W d) 1 :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (W.ι ≫ f)).homEquiv
    (𝒜 (Int.ofNat (1 * d)))
    (RingedSpace.TensorPower.sheaf (restrictedVeroneseLineBundle L W d) 1)).symm
      (restrictedDegreeHom 𝒜 f L ψ W d 1)

/-- The canonical restricted degreewise maps preserve the multiplicative unit. -/
theorem restrictedDegreeHom_map_one
    (W : T.Opens) (d : ℕ) (U : S.Opens) :
    (((restrictedDegreeHom 𝒜 f L ψ W d 0).val.app (op U)).hom
        (Eq.mp (RelativeProjDegreeQuadruple.sourceZeroSectionEq 𝒜 U d)
          (𝒜.one (op U)))) =
      TensorPower.oneSection W.toScheme.sheaf
        (restrictedVeroneseLineBundle L W d) (op ((W.ι ≫ f) ⁻¹ᵁ U)) := sorry

/-- The canonical restricted degreewise maps preserve multiplication of homogeneous
sections. -/
theorem restrictedDegreeHom_map_mul
    (W : T.Opens) (d : ℕ) (U : S.Opens) (i j : ℕ)
    (x : Γ(𝒜 (Int.ofNat (i * d)), U))
    (y : Γ(𝒜 (Int.ofNat (j * d)), U)) :
    (((restrictedDegreeHom 𝒜 f L ψ W d (i + j)).val.app (op U)).hom
        (Eq.mp (RelativeProjDegreeQuadruple.sourceMulSectionEq 𝒜 U i j d)
          (𝒜.mul (op U) (Int.ofNat (i * d)) (Int.ofNat (j * d)) x y))) =
      TensorPower.mulSection W.toScheme.sheaf
        (restrictedVeroneseLineBundle L W d) (op ((W.ι ≫ f) ⁻¹ᵁ U)) i j
          (((restrictedDegreeHom 𝒜 f L ψ W d i).val.app (op U)).hom x)
          (((restrictedDegreeHom 𝒜 f L ψ W d j).val.app (op U)).hom y) := sorry

/-- The canonical restricted degree-one map is adjoint to the degree-one component of the
restricted multiplicative map. -/
theorem restrictedDegreeMap_spec
    (W : T.Opens) (d : ℕ) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (W.ι ≫ f)).homEquiv
        (𝒜 (Int.ofNat (1 * d)))
        (RingedSpace.TensorPower.sheaf (restrictedVeroneseLineBundle L W d) 1)).toFun
          (restrictedDegreeMap 𝒜 f L ψ W d) =
      restrictedDegreeHom 𝒜 f L ψ W d 1 := sorry

/-- The fixed-degree quadruple canonically determined on an open where the restricted
degree-one map is epimorphic. -/
noncomputable def restrictedDegreeQuadruple
    (W : T.Opens) (d : ℕ)
    (degreeOne_surjective : Epi (restrictedDegreeMap 𝒜 f L ψ W d)) :
    RelativeProjDegreeQuadruple 𝒜 d W.toScheme :=
  RelativeProjDegreeQuadruple.of (𝒜 := 𝒜) (d := d) (W.ι ≫ f)
    (restrictedVeroneseLineBundle L W d) inferInstance (restrictedDegreeHom 𝒜 f L ψ W d)
    (restrictedDegreeHom_map_one 𝒜 f L ψ W d)
      (restrictedDegreeHom_map_mul 𝒜 f L ψ W d)
    (restrictedDegreeMap 𝒜 f L ψ W d) (restrictedDegreeMap_spec 𝒜 f L ψ W d)
      degreeOne_surjective

/-- A fixed-degree quadruple is the restriction of a graded section map when its structure
morphism, line bundle, every multiplicative component, and adjoint degree-one map are the
canonical restrictions. -/
def IsRestriction
    (W : T.Opens) (d : ℕ) (q : RelativeProjDegreeQuadruple 𝒜 d W.toScheme) : Prop :=
  q.morphism = W.ι ≫ f ∧
    q.lineBundle = restrictedVeroneseLineBundle L W d ∧
    (∀ n : ℕ, HEq (q.psi n) (restrictedDegreeHom 𝒜 f L ψ W d n)) ∧
    HEq q.degreeOneMap (restrictedDegreeMap 𝒜 f L ψ W d)

/-- Restriction to an open is exactly equality of the structure map and line bundle together
with all degreewise maps and the adjoint degree-one map. -/
theorem isRestriction_spec
    (W : T.Opens) (d : ℕ) (q : RelativeProjDegreeQuadruple 𝒜 d W.toScheme) :
    IsRestriction (𝒜 := 𝒜) (f := f) (L := L) (ψ := ψ) W d q ↔
      q.morphism = W.ι ≫ f ∧
        q.lineBundle = restrictedVeroneseLineBundle L W d ∧
        (∀ n : ℕ, HEq (q.psi n) (restrictedDegreeHom 𝒜 f L ψ W d n)) ∧
        HEq q.degreeOneMap (restrictedDegreeMap 𝒜 f L ψ W d) := sorry

/-- The canonical fixed-degree quadruple has precisely the prescribed restricted structure
map, line bundle, homogeneous components, and adjoint degree-one map. -/
theorem restrictedDegreeQuadruple_isRestriction
    (W : T.Opens) (d : ℕ)
    (degreeOne_surjective : Epi (restrictedDegreeMap 𝒜 f L ψ W d)) :
    IsRestriction (𝒜 := 𝒜) (f := f) (L := L) (ψ := ψ) W d
      (restrictedDegreeQuadruple 𝒜 f L ψ W d degreeOne_surjective) := sorry

/-- The homogeneous section over an affine base chart induced by the original multiplicative
map after restriction of the invertible module. -/
noncomputable def affineDegreeSection
    (U : S.affineOpens) (n : ℕ) (x : sectionGrading U n) :
    Γ(RingedSpace.TensorPower.sheaf
      ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) n, ⊤) :=
  (((Scheme.Modules.pullbackTensorPowerIso (f ⁻¹ᵁ (U : S.Opens)).ι L n).hom.val.app
        (op (⊤ : (f ⁻¹ᵁ (U : S.Opens)).toScheme.Opens))).hom)
    (((((Scheme.Modules.restrictFunctorIsoPullback
        (f ⁻¹ᵁ (U : S.Opens)).ι).hom.app
          (RingedSpace.TensorPower.sheaf L n)).val.app
            (op (⊤ : (f ⁻¹ᵁ (U : S.Opens)).toScheme.Opens))).hom)
      ((Scheme.Modules.restrictAppIso (f ⁻¹ᵁ (U : S.Opens)).ι
          (RingedSpace.TensorPower.sheaf L n) ⊤).inv
        (Eq.mp
          (congrArg
            (fun V : T.Opens ↦
              (Γ(RingedSpace.TensorPower.sheaf L n, V) : Type u))
            (Scheme.Opens.ι_image_top (f ⁻¹ᵁ (U : S.Opens))).symm)
          ((((@RingedSpace.InvertiblePower.natIso _ L
              (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L)) n).inv.val.app
                (op (f ⁻¹ᵁ (U : S.Opens)))).hom)
            ((Scheme.Modules.Hom.app (ψ.hom n) (U : S.Opens)).hom ((model U n).symm x))))))

/-- Affine compatibility identifies the restricted global domain, morphism, and twist map with
the unique absolute projective section map induced by the restricted line bundle and graded
sections. -/
structure AffineChartCompatibility
    (c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ)
    (U : S.affineOpens) where
  /-- The graded section map induced on the inverse image of the affine base chart. -/
  sectionMap : sectionGrading U →+*ᵍ RingedSpace.GradedSections.grading
    ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L)
  /-- Every homogeneous section is the restriction of the corresponding component of `ψ`. -/
  sectionMap_induced : ∀ n : ℕ, ∀ x : sectionGrading U n,
    projSectionMapDegreeSection (sectionGrading U)
        ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) sectionMap n x =
      affineDegreeSection (𝒜 := 𝒜) (sectionGrading := sectionGrading) (model := model)
        (f := f) (L := L) (ψ := ψ) (U := U) (n := n) (x := x)
  /-- The canonical absolute projective section map on the affine inverse image. -/
  localMap : ProjSectionMap (sectionGrading U)
    ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) (P U) sectionMap
  /-- The absolute projective section map has its canonical basic-open and degreewise behavior. -/
  localMap_isCanonical : localMap.IsCanonical
  /-- The restriction of the global domain is the natural domain of the affine section map. -/
  domainIso :
    (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).toScheme ≅
      (projSectionMapDomain (sectionGrading U)
        ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) sectionMap).toScheme
  /-- The domain identification commutes with the canonical inclusions into the source
  scheme. -/
  domain_over_source :
    domainIso.hom ≫
        (projSectionMapDomain (sectionGrading U)
          ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) sectionMap).ι ≫
        (f ⁻¹ᵁ (U : S.Opens)).ι =
      (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).ι ≫ c.domain.ι
  /-- Under the domain identification and the realization chart, the global map is the
  canonical absolute projective section map. -/
  map_eq : affineRestrictionMap (sectionGrading := sectionGrading) (R := R)
    (presentation := presentation) (f := f) (L := L) (ψ := ψ)
      (c := c) (U := U) =
    domainIso.hom ≫ localMap.map
  /-- The source of the pulled-back absolute twist comparison is identified with the
  restriction of the source of the global twist comparison. -/
  thetaSourceIso : ∀ n : ℕ,
    (Scheme.Modules.pullback domainIso.hom).obj
        (((P U).twistAlgebra.pullbackAlgebra localMap.map) (Int.ofNat n)) ≅
      (Scheme.Modules.pullback
        (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).ι).obj
          ((Scheme.Modules.pullback c.map).obj
            (presentation.twistAlgebra (Int.ofNat n)))
  /-- The target of the pulled-back absolute twist comparison is identified with the
  restriction of the target of the global twist comparison. -/
  thetaTargetIso : ∀ n : ℕ,
    (Scheme.Modules.pullback domainIso.hom).obj
        (pullbackInvertiblePowerGradedAlgebra
          (projSectionMapDomain (sectionGrading U)
            ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) sectionMap).ι
          ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) (Int.ofNat n)) ≅
      (Scheme.Modules.pullback
        (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).ι).obj
          (pullbackInvertiblePowerGradedAlgebra c.domain.ι L (Int.ofNat n))
  /-- In every nonnegative degree, the absolute twist comparison equals the restricted global
  twist comparison after transport through the canonical identifications. -/
  theta_eq : ∀ n : ℕ,
    (Scheme.Modules.pullback domainIso.hom).map
          (localMap.theta.hom (Int.ofNat n)) ≫
        (thetaTargetIso n).hom =
      (thetaSourceIso n).hom ≫
        (Scheme.Modules.pullback
          (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).ι).map
            (((Scheme.Modules.pullbackPushforwardAdjunction c.map).homEquiv
              (presentation.twistAlgebra (Int.ofNat n))
              (pullbackInvertiblePowerGradedAlgebra c.domain.ι L (Int.ofNat n))).symm
                (c.theta.hom n))

namespace AffineChartCompatibility

/-- Construct an affine compatibility from its induced section map, canonical absolute map,
domain comparison, morphism equality, and transported twist comparison. -/
def of
    {c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ}
    {U : S.affineOpens}
    (sectionMap : sectionGrading U →+*ᵍ RingedSpace.GradedSections.grading
      ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L))
    (sectionMap_induced : ∀ n : ℕ, ∀ x : sectionGrading U n,
      projSectionMapDegreeSection (sectionGrading U)
          ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) sectionMap n x =
        affineDegreeSection (𝒜 := 𝒜) (sectionGrading := sectionGrading) (model := model)
          (f := f) (L := L) (ψ := ψ) (U := U) (n := n) (x := x))
    (localMap : ProjSectionMap (sectionGrading U)
      ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) (P U) sectionMap)
    (localMap_isCanonical : localMap.IsCanonical)
    (domainIso :
      (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).toScheme ≅
        (projSectionMapDomain (sectionGrading U)
          ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) sectionMap).toScheme)
    (domain_over_source :
      domainIso.hom ≫
          (projSectionMapDomain (sectionGrading U)
            ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) sectionMap).ι ≫
          (f ⁻¹ᵁ (U : S.Opens)).ι =
        (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).ι ≫ c.domain.ι)
    (map_eq : affineRestrictionMap (sectionGrading := sectionGrading) (R := R)
      (presentation := presentation) (f := f) (L := L) (ψ := ψ)
        (c := c) (U := U) =
      domainIso.hom ≫ localMap.map)
    (thetaSourceIso : ∀ n : ℕ,
      (Scheme.Modules.pullback domainIso.hom).obj
          (((P U).twistAlgebra.pullbackAlgebra localMap.map) (Int.ofNat n)) ≅
        (Scheme.Modules.pullback
          (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).ι).obj
            ((Scheme.Modules.pullback c.map).obj
              (presentation.twistAlgebra (Int.ofNat n))))
    (thetaTargetIso : ∀ n : ℕ,
      (Scheme.Modules.pullback domainIso.hom).obj
          (pullbackInvertiblePowerGradedAlgebra
            (projSectionMapDomain (sectionGrading U)
              ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) sectionMap).ι
            ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) (Int.ofNat n)) ≅
        (Scheme.Modules.pullback
          (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).ι).obj
            (pullbackInvertiblePowerGradedAlgebra c.domain.ι L (Int.ofNat n)))
    (theta_eq : ∀ n : ℕ,
      (Scheme.Modules.pullback domainIso.hom).map
            (localMap.theta.hom (Int.ofNat n)) ≫
          (thetaTargetIso n).hom =
        (thetaSourceIso n).hom ≫
          (Scheme.Modules.pullback
            (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).ι).map
              (((Scheme.Modules.pullbackPushforwardAdjunction c.map).homEquiv
                (presentation.twistAlgebra (Int.ofNat n))
                (pullbackInvertiblePowerGradedAlgebra c.domain.ι L (Int.ofNat n))).symm
                  (c.theta.hom n))) :
    AffineChartCompatibility 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ c U where
  sectionMap := sectionMap
  sectionMap_induced := sectionMap_induced
  localMap := localMap
  localMap_isCanonical := localMap_isCanonical
  domainIso := domainIso
  domain_over_source := domain_over_source
  map_eq := map_eq
  thetaSourceIso := thetaSourceIso
  thetaTargetIso := thetaTargetIso
  theta_eq := theta_eq

/-- Affine compatibility simultaneously exposes the induced homogeneous sections, canonical
absolute map, domain inclusion, morphism comparison, and transported twist comparison. -/
theorem spec
    {c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ}
    {U : S.affineOpens}
    (a : AffineChartCompatibility 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ c U) :
    (∀ n : ℕ, ∀ x : sectionGrading U n,
      projSectionMapDegreeSection (sectionGrading U)
          ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) a.sectionMap n x =
        affineDegreeSection (𝒜 := 𝒜) (sectionGrading := sectionGrading) (model := model)
          (f := f) (L := L) (ψ := ψ) (U := U) (n := n) (x := x)) ∧
      a.localMap.IsCanonical ∧
      (a.domainIso.hom ≫
          (projSectionMapDomain (sectionGrading U)
            ((Scheme.Modules.pullback (f ⁻¹ᵁ (U : S.Opens)).ι).obj L) a.sectionMap).ι ≫
          (f ⁻¹ᵁ (U : S.Opens)).ι =
        (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).ι ≫ c.domain.ι) ∧
      affineRestrictionMap (sectionGrading := sectionGrading) (R := R)
          (presentation := presentation) (f := f) (L := L) (ψ := ψ)
            (c := c) (U := U) =
        a.domainIso.hom ≫ a.localMap.map ∧
      ∀ n : ℕ,
        (Scheme.Modules.pullback a.domainIso.hom).map
              (a.localMap.theta.hom (Int.ofNat n)) ≫
            (a.thetaTargetIso n).hom =
          (a.thetaSourceIso n).hom ≫
            (Scheme.Modules.pullback
              (c.map ⁻¹ᵁ (Scheme.relativeProjπ R ⁻¹ᵁ (U : S.Opens))).ι).map
                (((Scheme.Modules.pullbackPushforwardAdjunction c.map).homEquiv
                  (presentation.twistAlgebra (Int.ofNat n))
                  (pullbackInvertiblePowerGradedAlgebra c.domain.ι L
                    (Int.ofNat n))).symm (c.theta.hom n)) := sorry

end AffineChartCompatibility

/-- A relative projective section map is canonical when its twist comparison commutes with the
original graded map, its restriction agrees with every associated fixed-degree construction,
and every affine base chart is the canonical absolute projective section map. -/
def IsCanonical
    [F : RelativeProjFunctor S 𝒜]
    (associatedToQuadruples : ∀ d : {n : ℕ // 1 ≤ n},
      (F.degreeFunctor d).IsAssociatedToQuadruples)
    (representedPoint : F.toFunctor.obj (op (Scheme.relativeProj R)))
    (c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ) : Prop :=
  ThetaCompatible (𝒜 := 𝒜) (presentation := presentation)
      (f := f) (L := L) (ψ := ψ) (c := c) ∧
    (∀ (W : T.Opens) (d : ℕ) (hd : 1 ≤ d)
      (degreeOne_surjective : Epi (restrictedDegreeMap 𝒜 f L ψ W d)),
      ∃ hW : W ≤ c.domain,
        ∀ (r : W.toScheme ⟶ Scheme.relativeProj R),
          RelativeProjDegreeQuadruple.IsAssociatedMorphism hd
              (associatedToQuadruples ⟨d, hd⟩) (Scheme.relativeProjπ R)
              representedPoint
              (restrictedDegreeQuadruple 𝒜 f L ψ W d degreeOne_surjective) r →
            T.homOfLE hW ≫ c.map = r) ∧
    ∀ U : S.affineOpens,
      Nonempty (AffineChartCompatibility 𝒜 hqc A σ sectionGrading model hModel P
        sectionRestrict sectionRestrict_spec R presentation f L ψ c U)

/-- Canonicity is exactly the conjunction of the global theta square, all fixed-degree
restriction comparisons, and all affine-chart identifications. -/
theorem isCanonical_spec
    [F : RelativeProjFunctor S 𝒜]
    (associatedToQuadruples : ∀ d : {n : ℕ // 1 ≤ n},
      (F.degreeFunctor d).IsAssociatedToQuadruples)
    (representedPoint : F.toFunctor.obj (op (Scheme.relativeProj R)))
    (c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ) :
    IsCanonical (𝒜 := 𝒜) (associatedToQuadruples := associatedToQuadruples)
        (representedPoint := representedPoint) (c := c) ↔
      ThetaCompatible (𝒜 := 𝒜) (presentation := presentation)
          (f := f) (L := L) (ψ := ψ) (c := c) ∧
        (∀ (W : T.Opens) (d : ℕ) (hd : 1 ≤ d)
          (degreeOne_surjective : Epi (restrictedDegreeMap 𝒜 f L ψ W d)),
          ∃ hW : W ≤ c.domain,
            ∀ (r : W.toScheme ⟶ Scheme.relativeProj R),
              RelativeProjDegreeQuadruple.IsAssociatedMorphism hd
                  (associatedToQuadruples ⟨d, hd⟩) (Scheme.relativeProjπ R)
                  representedPoint
                  (restrictedDegreeQuadruple 𝒜 f L ψ W d degreeOne_surjective) r →
                T.homOfLE hW ≫ c.map = r) ∧
        ∀ U : S.affineOpens,
          Nonempty (AffineChartCompatibility 𝒜 hqc A σ sectionGrading model hModel P
            sectionRestrict sectionRestrict_spec R presentation f L ψ c U) := sorry

namespace IsCanonical

/-- In every nonnegative degree, the comparison with the relative twists makes the original
graded map commute after restriction to the canonical open domain. -/
theorem theta_commutes
    [F : RelativeProjFunctor S 𝒜]
    {associatedToQuadruples : ∀ d : {n : ℕ // 1 ≤ n},
      (F.degreeFunctor d).IsAssociatedToQuadruples}
    {representedPoint : F.toFunctor.obj (op (Scheme.relativeProj R))}
    {c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ}
    (hc : IsCanonical (𝒜 := 𝒜) (associatedToQuadruples := associatedToQuadruples)
      (representedPoint := representedPoint) (c := c))
    (n : ℕ) (U : S.Opens) (x : Γ(𝒜 (Int.ofNat n), U)) :
    (Scheme.Modules.Hom.app
        (presentation.psi.hom n ≫
          (Scheme.Modules.pushforward (Scheme.relativeProjπ R)).map (c.theta.hom n) ≫
          (Scheme.Modules.pushforwardComp c.map (Scheme.relativeProjπ R)).hom.app
            (pullbackInvertiblePowerGradedAlgebra c.domain.ι L (Int.ofNat n)) ≫
          (Scheme.Modules.pushforwardCongr c.map_over_base).hom.app
            (pullbackInvertiblePowerGradedAlgebra c.domain.ι L (Int.ofNat n))) U).hom x =
      (Scheme.Modules.Hom.app
        (ψ.hom n ≫
          (Scheme.Modules.pushforward f).map
            ((Scheme.Modules.pullbackPushforwardAdjunction c.domain.ι).unit.app
              (@RingedSpace.InvertiblePower.sheaf _ L
                (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L))
                (Int.ofNat n))) ≫
          (Scheme.Modules.pushforwardComp c.domain.ι f).hom.app
            ((Scheme.Modules.pullback c.domain.ι).obj
              (@RingedSpace.InvertiblePower.sheaf _ L
                (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L))
                (Int.ofNat n)))) U).hom x := sorry

/-- On every open where the canonical degree-`d` restriction is epimorphic, the restricted
canonical morphism equals any morphism associated to that fixed-degree quadruple. -/
theorem restrict_eq_of_isAssociatedMorphism
    [F : RelativeProjFunctor S 𝒜]
    {associatedToQuadruples : ∀ d : {n : ℕ // 1 ≤ n},
      (F.degreeFunctor d).IsAssociatedToQuadruples}
    {representedPoint : F.toFunctor.obj (op (Scheme.relativeProj R))}
    {c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ}
    (hc : IsCanonical (𝒜 := 𝒜) (associatedToQuadruples := associatedToQuadruples)
      (representedPoint := representedPoint) (c := c))
    (W : T.Opens) (d : ℕ) (hd : 1 ≤ d)
    (degreeOne_surjective : Epi (restrictedDegreeMap 𝒜 f L ψ W d))
    (r : W.toScheme ⟶ Scheme.relativeProj R)
    (hr : RelativeProjDegreeQuadruple.IsAssociatedMorphism hd
      (associatedToQuadruples ⟨d, hd⟩) (Scheme.relativeProjπ R)
      representedPoint
      (restrictedDegreeQuadruple 𝒜 f L ψ W d degreeOne_surjective) r) :
    ∃ hW : W ≤ c.domain, T.homOfLE hW ≫ c.map = r := sorry

/-- On every affine base chart, the restricted domain, morphism, and twist comparison agree
with the canonical absolute projective section map induced by the restricted graded sections. -/
theorem affineChart
    [F : RelativeProjFunctor S 𝒜]
    {associatedToQuadruples : ∀ d : {n : ℕ // 1 ≤ n},
      (F.degreeFunctor d).IsAssociatedToQuadruples}
    {representedPoint : F.toFunctor.obj (op (Scheme.relativeProj R))}
    {c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ}
    (hc : IsCanonical (𝒜 := 𝒜) (associatedToQuadruples := associatedToQuadruples)
      (representedPoint := representedPoint) (c := c))
    (U : S.affineOpens) :
    Nonempty (AffineChartCompatibility 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec R presentation f L ψ c U) := sorry

end IsCanonical

end RelativeProjSectionMap

/-- A multiplicative graded map into the integral powers of an invertible module determines a
unique relative projective section map satisfying the global, fixed-degree, and affine
characterizations. -/
theorem existsUnique_relativeProjSectionMap
    [F : RelativeProjFunctor S 𝒜]
    (associatedToQuadruples : ∀ d : {n : ℕ // 1 ≤ n},
      (F.degreeFunctor d).IsAssociatedToQuadruples)
    (representedPoint : F.toFunctor.obj (op (Scheme.relativeProj R)))
    (representedPoint_isUniversal : F.toFunctor.IsRepresentedBy representedPoint) :
    ∃! c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ,
      RelativeProjSectionMap.IsCanonical (𝒜 := 𝒜)
        (associatedToQuadruples := associatedToQuadruples)
        (representedPoint := representedPoint) (c := c) := sorry

end

end AlgebraicGeometry.Scheme.Modules
