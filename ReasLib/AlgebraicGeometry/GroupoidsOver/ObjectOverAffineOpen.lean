/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.DeformationSituation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Lifts

/-! # Objects over spectra in a fixed affine chart -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- An object over the spectrum of an algebra in a chosen affine open of the base. -/
structure ObjectOverAffineOpen (X : GroupoidsOver S) where
  /-- The ring of the affine chart. -/
  base : CommRingCat.{u}
  /-- The coefficient algebra over the chart. -/
  coefficient : CommAlgCat.{u} base
  /-- The immersion defining the affine chart. -/
  openImmersion : Spec base ⟶ S
  /-- The chart is open. -/
  isOpenImmersion : IsOpenImmersion openImmersion
  /-- The structure morphism of the coefficient spectrum. -/
  toS : Spec (CommRingCat.of coefficient) ⟶ S
  /-- The coefficient spectrum factors through the chosen chart. -/
  factor : Spec.map (CommRingCat.ofHom (algebraMap base coefficient)) ≫ openImmersion = toS
  /-- The object of the total category. -/
  obj : X.total
  /-- The object lies over the coefficient spectrum. -/
  over_obj : X.p.obj obj = Over.mk toS

namespace ObjectOverAffineOpen

variable {X : GroupoidsOver S}

/-- The underlying coefficient ring. -/
abbrev carrier (ξ : ObjectOverAffineOpen X) : Type u := ξ.coefficient

/-- The canonical algebra structure of the coefficient ring over the chart. -/
abbrev algebra (ξ : ObjectOverAffineOpen X) : Algebra ξ.base ξ.carrier :=
  ξ.coefficient.algebra

/-- The chart as a dependent pair of its ring and immersion. -/
abbrev chart (ξ : ObjectOverAffineOpen X) : Σ Λ : CommRingCat.{u}, Spec Λ ⟶ S :=
  ⟨ξ.base, ξ.openImmersion⟩

/-- The object over the coefficient spectrum, forgetting the chosen chart. -/
abbrev toObjectOverSpec (ξ : ObjectOverAffineOpen X) : ObjectOverSpec X where
  toCommRingCat := CommRingCat.of ξ.coefficient
  toS := ξ.toS
  mapsIntoAffineOpen :=
    ⟨Spec ξ.base, inferInstance, ξ.openImmersion, ξ.isOpenImmersion,
      Spec.map (CommRingCat.ofHom (algebraMap ξ.base ξ.coefficient)), ξ.factor⟩
  obj := ξ.obj
  over_obj := ξ.over_obj

/-- Equip an object over a spectrum with a chosen affine chart and algebra factorization. -/
def of (ξ : ObjectOverSpec X) (base : Type u) [CommRing base]
    (openImmersion : Spec (CommRingCat.of base) ⟶ S) [IsOpenImmersion openImmersion]
    [Algebra base ξ.carrier]
    (factor : Spec.map (CommRingCat.ofHom (algebraMap base ξ.carrier)) ≫
      openImmersion = ξ.toS) : ObjectOverAffineOpen X where
  base := CommRingCat.of base
  coefficient := CommAlgCat.of base ξ.carrier
  openImmersion := openImmersion
  isOpenImmersion := inferInstance
  toS := ξ.toS
  factor := factor
  obj := ξ.obj
  over_obj := ξ.over_obj

/-- The chart-to-coefficient algebra map as a bundled ring morphism. -/
abbrev algebraHom (ξ : ObjectOverAffineOpen X) :
    ξ.base ⟶ CommRingCat.of ξ.carrier :=
  CommRingCat.ofHom (algebraMap ξ.base ξ.carrier)

/-- A restriction arrow along a ring map between objects in the same affine chart. -/
structure Hom (ξ η : ObjectOverAffineOpen X)
    extends ObjectOverSpec.Hom ξ.toObjectOverSpec η.toObjectOverSpec where
  /-- Equality of the complete affine charts. -/
  chartEq : η.chart = ξ.chart

/-- The equality of the chart rings induced by equality of complete charts. -/
abbrev Hom.baseEq {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) : η.base = ξ.base :=
  congrArg Sigma.fst f.chartEq

/-- The target coefficient algebra transported to the common chart ring. -/
abbrev Hom.algebra {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    Algebra ξ.base η.carrier := f.baseEq ▸ η.algebra

/-- The structure map from the common chart ring to the target coefficient ring. -/
def Hom.algebraHom {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    ξ.base ⟶ CommRingCat.of η.carrier :=
  CommRingCat.ofHom (@algebraMap ξ.base η.carrier _ _ f.algebra)

/-- The target structure morphism factors through the common affine chart. -/
theorem Hom.sourceFactor {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    Spec.map f.algebraHom ≫ ξ.openImmersion = η.toS := by
  rcases ξ with ⟨R, A, i, hi, a, ha, x, hx⟩
  rcases η with ⟨T, B, j, hj, b, hb, y, hy⟩
  rcases f with ⟨f, h⟩
  dsimp [chart] at h
  cases h
  exact hb

/-- The algebra homomorphism underlying a restriction arrow in a common chart. -/
def Hom.algHom {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    @AlgHom ξ.base ξ.carrier η.carrier _ _ _ ξ.algebra f.algebra :=
  @AlgHom.mk ξ.base ξ.carrier η.carrier _ _ _ ξ.algebra f.algebra
    f.toRingHom (by sorry)

/-- The underlying ring map of the common-chart algebra homomorphism is the stored ring map. -/
theorem Hom.algHom_toRingHom {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    @AlgHom.toRingHom ξ.base ξ.carrier η.carrier _ _ _ ξ.algebra f.algebra f.algHom =
      f.toRingHom := rfl

/-- The identity restriction arrow in an affine chart. -/
def Hom.id (ξ : ObjectOverAffineOpen X) : Hom ξ ξ where
  toHom := ObjectOverSpec.Hom.id ξ.toObjectOverSpec
  chartEq := rfl

/-- The composite of two restriction arrows in a common affine chart. -/
def Hom.comp {ξ η ζ : ObjectOverAffineOpen X} (f : Hom ξ η) (g : Hom η ζ) :
    Hom ξ ζ where
  toHom := ObjectOverSpec.Hom.comp f.toHom g.toHom
  chartEq := g.chartEq.trans f.chartEq

/-- The comparison fibre arrow induced by cartesian factorization of a restriction arrow. -/
def Hom.fiberArrow {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    Chosen.reindexObj X.p
      (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
      ξ.toObjectOverSpec.toFiber ⟶ η.toObjectOverSpec.toFiber := by
  have laws :
      (X.p.IsHomLift
        (𝟙 (Over.mk η.toS) ≫ specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
        f.restriction) ∧
      (∀ h : X.p.IsHomLift
          (𝟙 (Over.mk η.toS) ≫ specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
          f.restriction,
        X.p.IsHomLift (𝟙 (Over.mk η.toS))
          (FiberedCategoryOver.Groupoids.cartesianFactorOf X.p
            (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
            (𝟙 (Over.mk η.toS)) ξ.toObjectOverSpec.toFiber f.restriction h)) := by sorry
  let arrow := FiberedCategoryOver.Groupoids.cartesianFactorOf X.p
    (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
    (𝟙 (Over.mk η.toS)) ξ.toObjectOverSpec.toFiber f.restriction laws.1
  have vertical : X.p.IsHomLift (𝟙 (Over.mk η.toS)) arrow := laws.2 laws.1
  exact CategoryTheory.inv
    (⟨arrow, vertical⟩ : η.toObjectOverSpec.toFiber ⟶
      Chosen.reindexObj X.p
        (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
        ξ.toObjectOverSpec.toFiber)

/-- The inverse comparison fibre arrow factors the original restriction through the cartesian arrow. -/
theorem Hom.fiberArrow_fac {ξ η : ObjectOverAffineOpen X} (f : Hom ξ η) :
    Fiber.fiberInclusion.map (CategoryTheory.inv f.fiberArrow) ≫
      Chosen.cartesianHom X.p
        (specOverHom (CommRingCat.ofHom f.toRingHom) f.toS_comp)
        ξ.toObjectOverSpec.toFiber = f.restriction := sorry

/-- The universal-property comparison from bundled differentials to algebra differentials. -/
def kaehlerCompare (ξ : ObjectOverAffineOpen X) :
    CommRingCat.KaehlerDifferential ξ.algebraHom ⟶ ModuleCat.of ξ.carrier Ω[ξ.carrier ⁄ ξ.base] := by
  have laws : (∀ a b : ξ.carrier,
      KaehlerDifferential.D ξ.base ξ.carrier (a + b) =
        KaehlerDifferential.D ξ.base ξ.carrier a + KaehlerDifferential.D ξ.base ξ.carrier b) ∧
      (∀ a b : ξ.carrier,
        KaehlerDifferential.D ξ.base ξ.carrier (a * b) =
          a • KaehlerDifferential.D ξ.base ξ.carrier b +
            b • KaehlerDifferential.D ξ.base ξ.carrier a) ∧
      (∀ a : ξ.base, KaehlerDifferential.D ξ.base ξ.carrier (ξ.algebraHom a) = 0) := by
    sorry
  exact ModuleCat.Derivation.desc
    (ModuleCat.Derivation.mk (fun b ↦ KaehlerDifferential.D ξ.base ξ.carrier b)
      laws.1 laws.2.1 laws.2.2)

/-- The comparison of differentials sends the universal differential to the usual algebra differential. -/
theorem kaehlerCompare_d (ξ : ObjectOverAffineOpen X) (a : ξ.carrier) :
    kaehlerCompare ξ (CommRingCat.KaehlerDifferential.d (f := ξ.algebraHom) a) =
      KaehlerDifferential.D ξ.base ξ.carrier a := sorry

end ObjectOverAffineOpen

namespace DeformationSituation

variable {X : GroupoidsOver S}

/-- A square-zero deformation situation over a chosen affine-open object. -/
structure OverAffine (ξ : ObjectOverAffineOpen X) where
  /-- The underlying square-zero deformation situation. -/
  situation : DeformationSituation X
  /-- Its object over the spectrum agrees with the chosen object. -/
  isOver : situation.toObjectOverSpec = ξ.toObjectOverSpec
  /-- The algebra structure on the extension ring over the chart ring. -/
  algebra : Algebra ξ.base situation.source
  /-- The extension spectrum factors through the same chart. -/
  sourceFactor : Spec.map (CommRingCat.ofHom
      (@algebraMap ξ.base situation.source _ _ algebra)) ≫
        ξ.openImmersion = situation.sourceToS

/-- The square-zero extension map transported to the chosen coefficient ring. -/
def OverAffine.toCarrierOver {ξ : ObjectOverAffineOpen X} (τ : OverAffine ξ) :
    τ.situation.source →+* ξ.carrier := by
  let action := fun x ↦
    cast (congrArg ObjectOverSpec.carrier τ.isOver) (τ.situation.toCarrier x)
  have laws : action 1 = 1 ∧ (∀ a b, action (a * b) = action a * action b) ∧
      action 0 = 0 ∧ (∀ a b, action (a + b) = action a + action b) := by sorry
  exact
    { toFun := action
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2 }

/-- Evaluation of the transported square-zero extension map is transport of the original value. -/
theorem OverAffine.toCarrierOver_eq {ξ : ObjectOverAffineOpen X}
    (τ : OverAffine ξ) (x : τ.situation.source) :
    τ.toCarrierOver x =
      cast (congrArg ObjectOverSpec.carrier τ.isOver) (τ.situation.toCarrier x) := rfl

/-- The square-zero extension map as an algebra map over the affine chart. -/
def OverAffine.algHom {ξ : ObjectOverAffineOpen X} (τ : OverAffine ξ) :
    @AlgHom ξ.base τ.situation.source ξ.carrier _ _ _ τ.algebra ξ.algebra :=
  @AlgHom.mk ξ.base τ.situation.source ξ.carrier _ _ _ τ.algebra ξ.algebra
    τ.toCarrierOver (by sorry)

/-- The affine algebra map has the transported square-zero map as its underlying ring map. -/
theorem OverAffine.algHom_toRingHom {ξ : ObjectOverAffineOpen X} (τ : OverAffine ξ) :
    @AlgHom.toRingHom ξ.base τ.situation.source ξ.carrier _ _ _ τ.algebra ξ.algebra
      τ.algHom = τ.toCarrierOver := rfl

end DeformationSituation

end AlgebraicGeometry.GroupoidsOver
