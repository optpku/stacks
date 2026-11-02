/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.Extension.Cotangent.Surjective
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Lifts
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.SquareZeroComparison
public import ReasLib.AlgebraicGeometry.Deformation.SquareZero
public import ReasLib.AlgebraicGeometry.GroupoidsOver.DualObstruction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.DeformationSituation.FixedObject

/-!
# Naive cotangent evaluations of dual obstruction classes

Evaluation of a class in `H¹(K ⊗^L NL{A⁄Λ})` along `NL{A⁄Λ} ⟶ I⟦1⟧` and
along `NL{A⁄Λ} ⟶ Ω{A⁄Λ}`, together with the connecting map of a short exact
sequence of kernels and compatibility of obstruction classes with its connecting map.
-/

@[expose] public section

open scoped Module.CommOpposite

open CategoryTheory AlgebraicGeometry Functor
open HomologicalComplex ComplexShape AlgebraicGeometry.Deformation
open CategoryTheory.Pretriangulated
open MvPolynomial
open scoped NaiveCotangent

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

section HomologyTensorDerived

variable {A : Type u} [CommRing A]

/-- The `n`-th homology of the derived tensor of a complex `K` with an object of
`D(A)`. -/
def homologyTensorDerived (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (X : DerivedCategory (ModuleCat.{u} A)) : ModuleCat.{u} A :=
  (DerivedCategory.homologyFunctor (ModuleCat A) n).obj
    ((DerivedCategory.derivedTensorProduct (DerivedCategory.Q.obj K)).obj X)

/-- `homologyTensorDerived K n X` is homology of the derived tensor of `X` with
`K`. -/
theorem homologyTensorDerived_eq (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (X : DerivedCategory (ModuleCat.{u} A)) :
    homologyTensorDerived K n X =
      (DerivedCategory.homologyFunctor (ModuleCat A) n).obj
        ((DerivedCategory.derivedTensorProduct (DerivedCategory.Q.obj K)).obj X) :=
  sorry

end HomologyTensorDerived

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

namespace DeformationSituation

/-- The object of `X` obtained by reindexing a lift along a source ring map. -/
def ObjectLift.reindexObj {σ τ : DeformationSituation X} (f : Hom σ τ)
    (ℓ : ObjectLift σ) : X.total :=
  (Chosen.reindexObj X.p
    (specOverHom (CommRingCat.ofHom f.toSourceHom) f.sourceToS_comp)
    (Fiber.mk <|
      @IsHomLift.codomain_eq _ _ _ _ X.p _ _ σ.obj ℓ.obj' (thickening σ) ℓ.hom
        ℓ.isHomLift)).1

private theorem ObjectLift.restrict_laws {σ τ : DeformationSituation X} (f : Hom σ τ)
    (ℓ : ObjectLift σ) :
    (X.p.IsHomLift (thickening τ ≫ (specOverHom (CommRingCat.ofHom f.toSourceHom) f.sourceToS_comp)) (f.restriction ≫ ℓ.hom)) ∧
    (∀ (h : X.p.IsHomLift (thickening τ ≫ (specOverHom (CommRingCat.ofHom f.toSourceHom) f.sourceToS_comp))
        (f.restriction ≫ ℓ.hom)),
      X.p.IsHomLift (thickening τ)
        (FiberedCategoryOver.Groupoids.cartesianFactorOf X.p (specOverHom (CommRingCat.ofHom f.toSourceHom) f.sourceToS_comp)
          (thickening τ) (Fiber.mk <|
        @IsHomLift.codomain_eq _ _ _ _ X.p _ _ σ.obj ℓ.obj' (thickening σ) ℓ.hom
          ℓ.isHomLift) (f.restriction ≫ ℓ.hom) h)) :=
  sorry

/-- Restriction of an object lift along a morphism of deformation situations,
by cartesian reindexing of the lifted object. -/
def ObjectLift.restrict {σ τ : DeformationSituation X} (f : Hom σ τ)
    (ℓ : ObjectLift σ) : ObjectLift τ :=
  ObjectLift.of τ (ObjectLift.reindexObj f ℓ)
    (FiberedCategoryOver.Groupoids.cartesianFactorOf X.p
      (specOverHom (CommRingCat.ofHom f.toSourceHom) f.sourceToS_comp)
      (thickening τ)
      (Fiber.mk <|
        @IsHomLift.codomain_eq _ _ _ _ X.p _ _ σ.obj ℓ.obj' (thickening σ) ℓ.hom
          ℓ.isHomLift)
      (f.restriction ≫ ℓ.hom) (by exact (ObjectLift.restrict_laws f ℓ).1))
    (by exact (ObjectLift.restrict_laws f ℓ).2 (ObjectLift.restrict_laws f ℓ).1)

/-- The restricted lift is obtained by cartesian reindexing of the original
lifted object. -/
theorem ObjectLift.restrict_obj' {σ τ : DeformationSituation X} (f : Hom σ τ)
    (ℓ : ObjectLift σ) :
    (ObjectLift.restrict f ℓ).obj' = ObjectLift.reindexObj f ℓ :=
  sorry

private theorem ObjectLift.toLifts_laws {σ : DeformationSituation X} (ℓ : ObjectLift σ) :
    X.p.IsHomLift (specOverHom (CommRingCat.ofHom σ.toCarrier) σ.toS_comp) ℓ.hom :=
  sorry

/-- Convert an object lift into an isomorphism class in `Lift(x, A')`. -/
def ObjectLift.toLifts {σ : DeformationSituation X} (ℓ : ObjectLift σ) :
    lifts (Spectrum.ObjectOverSpec.toFiber σ.toObjectOverSpec) (CommRingCat.ofHom σ.toCarrier) σ.toS_comp :=
  lifts.mk <|
    @UnderLift.ofHom _ _ _ _ X.p _ _
      (specOverHom (CommRingCat.ofHom σ.toCarrier) σ.toS_comp)
      (Spectrum.ObjectOverSpec.toFiber σ.toObjectOverSpec) ℓ.obj' ℓ.hom (by exact ObjectLift.toLifts_laws ℓ)

/-- `ObjectLift.toLifts` is the class of the packaged under-lift. -/
theorem ObjectLift.toLifts_eq {σ : DeformationSituation X} (ℓ : ObjectLift σ) :
    ObjectLift.toLifts ℓ =
      lifts.mk
        (@UnderLift.ofHom _ _ _ _ X.p _ _
          (specOverHom (CommRingCat.ofHom σ.toCarrier) σ.toS_comp)
          (Spectrum.ObjectOverSpec.toFiber σ.toObjectOverSpec) ℓ.obj' ℓ.hom (by exact ObjectLift.toLifts_laws ℓ)) :=
  sorry

end DeformationSituation

namespace DualObstruction

/-- The structure morphism `Λ ⟶ A` of dual obstruction data, as a morphism of
commutative rings. -/
def baseHom (𝒟 : DualObstruction X) :
    CommRingCat.of 𝒟.base ⟶ CommRingCat.of 𝒟.carrier :=
  CommRingCat.ofHom (algebraMap 𝒟.base 𝒟.carrier)

/-- `baseHom` is `algebraMap` of the stored factorization through `Spec(Λ)`. -/
theorem baseHom_eq (𝒟 : DualObstruction X) :
    𝒟.baseHom = CommRingCat.ofHom (algebraMap 𝒟.base 𝒟.carrier) :=
  sorry

/-- The Kähler module `Ω{A⁄Λ}` attached to dual obstruction data. -/
def kaehler (𝒟 : DualObstruction X) : ModuleCat.{u} 𝒟.carrier :=
  CommRingCat.KaehlerDifferential 𝒟.baseHom

/-- `kaehler` is `CommRingCat.KaehlerDifferential` of `baseHom`. -/
theorem kaehler_eq (𝒟 : DualObstruction X) :
    𝒟.kaehler = CommRingCat.KaehlerDifferential 𝒟.baseHom :=
  sorry

/-- Image of `Spec(A') → S` lies in the affine open `Spec(Λ)`, since the
nilpotent thickening is a homeomorphism onto `Spec(A)` and `Spec(A) → S`
factors through `𝒟.openImmersion`. -/
theorem sourceToS_range_subset_openImmersion (𝒟 : DualObstruction X)
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    Set.range σ.sourceToS ⊆ Set.range 𝒟.openImmersion :=
  sorry

/-- The unique scheme morphism `Spec(A') ⟶ Spec(Λ)` lifting `sourceToS` through
the open immersion. -/
def sourceSpecHom (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    Spec (CommRingCat.of σ.source) ⟶ Spec (CommRingCat.of 𝒟.base) :=
  IsOpenImmersion.lift 𝒟.openImmersion σ.sourceToS
    (𝒟.sourceToS_range_subset_openImmersion hσ)

/-- `sourceSpecHom` recovers `sourceToS` after composing with the open
immersion. -/
theorem sourceSpecHom_comp (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.sourceSpecHom hσ ≫ 𝒟.openImmersion = σ.sourceToS :=
  sorry

/-- The structure map `Λ → A'` of a deformation situation over `𝒟`, obtained by
factoring `σ.sourceToS` through `𝒟.openImmersion`. -/
def sourceBaseHom (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) : 𝒟.base →+* σ.source :=
  (Spec.preimage (𝒟.sourceSpecHom hσ)).hom

/-- `sourceBaseHom` is the ring map underlying `sourceSpecHom`. -/
theorem sourceBaseHom_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.sourceBaseHom hσ = (Spec.preimage (𝒟.sourceSpecHom hσ)).hom :=
  sorry

/-- `Spec.map` of `sourceBaseHom` recovers `sourceToS` after the open
immersion. -/
theorem sourceBaseHom_comp_openImmersion (𝒟 : DualObstruction X)
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    Spec.map (CommRingCat.ofHom (𝒟.sourceBaseHom hσ)) ≫ 𝒟.openImmersion =
      σ.sourceToS :=
  sorry

/-- `sourceBaseHom` is the unique ring map `Λ → A'` factoring `sourceToS`
through the open immersion. -/
theorem sourceBaseHom_unique (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) (f : 𝒟.base →+* σ.source)
    (hf : Spec.map (CommRingCat.ofHom f) ≫ 𝒟.openImmersion = σ.sourceToS) :
    f = 𝒟.sourceBaseHom hσ :=
  sorry

/-- The composite `toCarrierOver ∘ sourceBaseHom` is `algebraMap Λ A`. -/
theorem sourceBaseHom_comp_toCarrierOver (𝒟 : DualObstruction X)
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    (DeformationSituation.toCarrierOver hσ).comp (𝒟.sourceBaseHom hσ) =
      algebraMap 𝒟.base 𝒟.carrier :=
  sorry

/-- The `Λ`-algebra structure on `A'` determined by `sourceBaseHom`. -/
abbrev sourceBaseAlgebra (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) : Algebra 𝒟.base σ.source :=
  (𝒟.sourceBaseHom hσ).toAlgebra

/-- `sourceBaseAlgebra` is `toAlgebra` of `sourceBaseHom`. -/
theorem sourceBaseAlgebra_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.sourceBaseAlgebra hσ = (𝒟.sourceBaseHom hσ).toAlgebra :=
  sorry

private theorem sourceAlgHom_laws (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    ∀ r : 𝒟.base, DeformationSituation.toCarrierOver hσ
      (@algebraMap 𝒟.base σ.source _ _ (𝒟.sourceBaseAlgebra hσ) r) =
        algebraMap 𝒟.base 𝒟.carrier r :=
  sorry

/-- The Λ-algebra map of a deformation situation for its geometric source algebra. -/
abbrev sourceAlgHom (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    @AlgHom 𝒟.base σ.source 𝒟.carrier _ _ _ (𝒟.sourceBaseAlgebra hσ) 𝒟.algebra :=
  @AlgHom.mk 𝒟.base σ.source 𝒟.carrier _ _ _ (𝒟.sourceBaseAlgebra hσ) 𝒟.algebra
    (DeformationSituation.toCarrierOver hσ) (by exact sourceAlgHom_laws 𝒟 hσ)

/-- The geometric source algebra homomorphism has the transported extension map. -/
theorem sourceAlgHom_toRingHom (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    (@AlgHom.toRingHom 𝒟.base σ.source 𝒟.carrier _ _ _
      (𝒟.sourceBaseAlgebra hσ) 𝒟.algebra (𝒟.sourceAlgHom hσ)) = DeformationSituation.toCarrierOver hσ :=
  sorry

/-- The `A'`-algebra structure on `A` induced by the stored square-zero map. -/
abbrev sourceAlgebra (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    Algebra σ.source 𝒟.carrier :=
  (DeformationSituation.toCarrierOver hσ).toAlgebra

/-- `sourceAlgebra` is `toAlgebra` of `toCarrierOver`. -/
theorem sourceAlgebra_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.sourceAlgebra hσ = (DeformationSituation.toCarrierOver hσ).toAlgebra :=
  sorry

/-- The scalar tower `Λ → A' → A` determined by `sourceAlgHom`. -/
abbrev sourceTower (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    @IsScalarTower 𝒟.base σ.source 𝒟.carrier
      (𝒟.sourceBaseAlgebra hσ).toSMul (𝒟.sourceAlgebra hσ).toSMul _ :=
  @IsScalarTower.of_algHom 𝒟.base σ.source 𝒟.carrier _ _ _
    (𝒟.sourceBaseAlgebra hσ) 𝒟.algebra (𝒟.sourceAlgHom hσ)

/-- The source scalar tower is induced by the geometric algebra homomorphism. -/
theorem sourceTower_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.sourceTower hσ =
      @IsScalarTower.of_algHom 𝒟.base σ.source 𝒟.carrier _ _ _
        (𝒟.sourceBaseAlgebra hσ) 𝒟.algebra (𝒟.sourceAlgHom hσ) :=
  sorry

/-- The universal derivation of `kaehler` as a `Λ`-derivation on `A`. -/
def kaehlerDerivation (𝒟 : DualObstruction X) :
    𝒟.kaehler.Derivation 𝒟.baseHom :=
  CommRingCat.KaehlerDifferential.D 𝒟.baseHom

/-- `kaehlerDerivation` evaluates as the canonical differential map. -/
theorem kaehlerDerivation_apply (𝒟 : DualObstruction X) (a : 𝒟.carrier) :
    𝒟.kaehlerDerivation.d a = CommRingCat.KaehlerDifferential.d (f := 𝒟.baseHom) a :=
  sorry

private theorem toKaehlerChain_laws (𝒟 : DualObstruction X) :
    let d : (Algebra.naiveCotangent 𝒟.base 𝒟.carrier).X 0 → 𝒟.kaehler :=
      fun x : (Algebra.naiveCotangent 𝒟.base 𝒟.carrier).X 0 ↦
      ((Algebra.Generators.self 𝒟.base 𝒟.carrier).cotangentSpaceBasis.repr x).sum
        fun a c ↦ c • 𝒟.kaehlerDerivation.d a
    (∀ x y, d (x + y) = d x + d y) ∧
    (∀ (c : 𝒟.carrier) x, d (c • x) = c • d x) ∧
    (∀ (ha : ∀ x y, d (x + y) = d x + d y)
      (hs : ∀ (c : 𝒟.carrier) x, d (c • x) = c • d x),
      (Algebra.naiveCotangent 𝒟.base 𝒟.carrier).d 1 0 ≫
        ConcreteCategory.ofHom ({ toFun := d, map_add' := ha, map_smul' := hs } :
          (Algebra.naiveCotangent 𝒟.base 𝒟.carrier).X 0 →ₗ[𝒟.carrier] 𝒟.kaehler) = 0) :=
  sorry

/-- The canonical chain map `NL{A⁄Λ} ⟶ Ω{A⁄Λ}[0]`. -/
def toKaehlerChain (𝒟 : DualObstruction X) :
    Algebra.naiveCotangent 𝒟.base 𝒟.carrier ⟶
      (ChainComplex.single₀ (ModuleCat.{u} 𝒟.carrier)).obj 𝒟.kaehler :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ConcreteCategory.ofHom
      { toFun := fun x ↦
          ((Algebra.Generators.self 𝒟.base 𝒟.carrier).cotangentSpaceBasis.repr x).sum
            fun a c ↦ c • 𝒟.kaehlerDerivation.d a
        map_add' := by exact (toKaehlerChain_laws 𝒟).1
        map_smul' := by exact (toKaehlerChain_laws 𝒟).2.1 },
      (by exact (toKaehlerChain_laws 𝒟).2.2 (toKaehlerChain_laws 𝒟).1 (toKaehlerChain_laws 𝒟).2.1)⟩

/-- `toKaehlerChain` is the unique chain map induced by `toKaehler` in degree
zero. -/
theorem toKaehlerChain_eq (𝒟 : DualObstruction X) :
    𝒟.toKaehlerChain =
      (ChainComplex.toSingle₀Equiv _ _).symm
        ⟨ConcreteCategory.ofHom
          { toFun := fun x ↦
              ((Algebra.Generators.self 𝒟.base 𝒟.carrier).cotangentSpaceBasis.repr x).sum
                fun a c ↦ c • 𝒟.kaehlerDerivation.d a
            map_add' := by exact (toKaehlerChain_laws 𝒟).1
            map_smul' := by exact (toKaehlerChain_laws 𝒟).2.1 },
          (by exact (toKaehlerChain_laws 𝒟).2.2 (toKaehlerChain_laws 𝒟).1 (toKaehlerChain_laws 𝒟).2.1)⟩ :=
  sorry

/-- Comparison of the unbundled Kähler module `Ω{A⁄Λ}` with `CommRingCat.KaehlerDifferential` of the
bundled algebra map `baseHom`. -/
def kaehlerCompare (𝒟 : DualObstruction X) :
    ModuleCat.of 𝒟.carrier Ω[𝒟.carrier ⁄ 𝒟.base] ⟶ 𝒟.kaehler :=
  by
    let differentials (a : Algebra 𝒟.base 𝒟.carrier) : ModuleCat.{u} 𝒟.carrier :=
      @ModuleCat.of 𝒟.carrier _ (@KaehlerDifferential 𝒟.base 𝒟.carrier _ _ a)
        inferInstance
        (@KaehlerDifferential.module' 𝒟.base 𝒟.carrier _ _ a 𝒟.carrier _
          (Algebra.id 𝒟.carrier)
          ⟨fun r s t ↦ by
            simp only [a.smul_def']
            exact mul_left_comm _ _ _⟩)
    have h : 𝒟.baseHom.hom.toAlgebra = 𝒟.algebra := toAlgebra_algebraMap
    exact eqToHom (congrArg differentials h.symm)

/-- The self-presentation augmentation `d ≫ toKaehler` vanishes. -/
theorem toKaehler_comp_d (𝒟 : DualObstruction X) :
    (Algebra.naiveCotangent 𝒟.base 𝒟.carrier).d 1 0 ≫
      ModuleCat.ofHom
        (Algebra.Generators.self 𝒟.base 𝒟.carrier).toExtension.toKaehler = 0 :=
  sorry

/-- The derived morphism `NL{A⁄Λ} ⟶ Ω{A⁄Λ}` in `D(A)`, as the self-presentation
augmentation `Extension.toKaehler` transported to `CommRingCat.KaehlerDifferential`. -/
def toKaehler (𝒟 : DualObstruction X) :
    Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier ⟶ ModuleCat.single0 𝒟.kaehler :=
  DerivedCategory.Q.map
    (extendMap
        ((ChainComplex.toSingle₀Equiv (Algebra.naiveCotangent 𝒟.base 𝒟.carrier)
            (ModuleCat.of 𝒟.carrier Ω[𝒟.carrier ⁄ 𝒟.base])).symm
          ⟨ModuleCat.ofHom
            (Algebra.Generators.self 𝒟.base 𝒟.carrier).toExtension.toKaehler,
            𝒟.toKaehler_comp_d⟩)
        embeddingDownNat ≫
      (extendSingleIso embeddingDownNat
        (ModuleCat.of 𝒟.carrier Ω[𝒟.carrier ⁄ 𝒟.base])
        (0 : ℕ) (0 : ℤ) rfl).hom) ≫
    (DerivedCategory.singleFunctor (ModuleCat 𝒟.carrier) 0).map 𝒟.kaehlerCompare

/-- `toKaehler` is the self-presentation `Extension.toKaehler` followed by
`kaehlerCompare`. -/
theorem toKaehler_eq (𝒟 : DualObstruction X) :
    𝒟.toKaehler =
      DerivedCategory.Q.map
        (extendMap
            ((ChainComplex.toSingle₀Equiv (Algebra.naiveCotangent 𝒟.base 𝒟.carrier)
                (ModuleCat.of 𝒟.carrier Ω[𝒟.carrier ⁄ 𝒟.base])).symm
              ⟨ModuleCat.ofHom
                (Algebra.Generators.self 𝒟.base 𝒟.carrier).toExtension.toKaehler,
                𝒟.toKaehler_comp_d⟩)
            embeddingDownNat ≫
          (extendSingleIso embeddingDownNat
            (ModuleCat.of 𝒟.carrier Ω[𝒟.carrier ⁄ 𝒟.base])
            (0 : ℕ) (0 : ℤ) rfl).hom) ≫
        (DerivedCategory.singleFunctor (ModuleCat 𝒟.carrier) 0).map 𝒟.kaehlerCompare :=
  sorry

/-- The structure map `A' → A` of a deformation situation over `𝒟` is
surjective. -/
theorem algebraMap_source_surjective (𝒟 : DualObstruction X)
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    Function.Surjective (@algebraMap σ.source 𝒟.carrier _ _ (𝒟.sourceAlgebra hσ)) :=
  letI := 𝒟.sourceAlgebra hσ
  (DeformationSituation.toCarrierOverMap hσ).property.surjective

/-- The empty-generator presentation of the stored square-zero surjection `A' → A`. -/
def surjectiveGenerators (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    @Algebra.Generators σ.source 𝒟.carrier PEmpty.{u + 1} _ _ (𝒟.sourceAlgebra hσ) :=
  @Algebra.Generators.ofSurjectiveAlgebraMap σ.source 𝒟.carrier _ _ (𝒟.sourceAlgebra hσ)
    (𝒟.algebraMap_source_surjective hσ)

/-- `surjectiveGenerators` is `ofSurjectiveAlgebraMap` of `sourceAlgebra`. -/
theorem surjectiveGenerators_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.surjectiveGenerators hσ =
      @Algebra.Generators.ofSurjectiveAlgebraMap σ.source 𝒟.carrier _ _
        (𝒟.sourceAlgebra hσ) (𝒟.algebraMap_source_surjective hσ) :=
  sorry

/-- The naive cotangent complex of `A' → A` for the stored square-zero algebra
structure. -/
abbrev naiveCotangentOver (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    ChainComplex (ModuleCat.{u} 𝒟.carrier) ℕ :=
  @Algebra.naiveCotangent σ.source 𝒟.carrier _ _ (𝒟.sourceAlgebra hσ)

/-- `naiveCotangentOver` is the self-presentation complex of `sourceAlgebra`. -/
theorem naiveCotangentOver_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.naiveCotangentOver hσ =
      @Algebra.naiveCotangent σ.source 𝒟.carrier _ _ (𝒟.sourceAlgebra hσ) :=
  sorry

/-- The empty-generator naive cotangent complex of the stored square-zero
surjection. -/
abbrev surjectiveComplex (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    ChainComplex (ModuleCat.{u} 𝒟.carrier) ℕ :=
  @Algebra.Extension.NaiveCotangent.complex σ.source 𝒟.carrier _ _
    (𝒟.sourceAlgebra hσ) (@Algebra.Generators.toExtension σ.source 𝒟.carrier PEmpty.{u + 1} _ _ (𝒟.sourceAlgebra hσ) (𝒟.surjectiveGenerators hσ))

/-- `surjectiveComplex` is the presentation complex of `surjectiveGenerators`. -/
theorem surjectiveComplex_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.surjectiveComplex hσ =
      @Algebra.Extension.NaiveCotangent.complex σ.source 𝒟.carrier _ _
    (𝒟.sourceAlgebra hσ) (@Algebra.Generators.toExtension σ.source 𝒟.carrier PEmpty.{u + 1} _ _ (𝒟.sourceAlgebra hσ) (𝒟.surjectiveGenerators hσ)) :=
  sorry

/-- The lifted conormal module, bundled as the degree-one term of the empty-generator complex. -/
abbrev surjectiveLiftModule (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) : ModuleCat.{u} 𝒟.carrier :=
  (𝒟.surjectiveComplex hσ).X 1

/-- The carrier of the lifted conormal module. -/
abbrev surjectiveLift (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) : Type u :=
  𝒟.surjectiveLiftModule hσ

/-- The lifted conormal carrier is the lifted conormal of the empty-generator presentation. -/
theorem surjectiveLift_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.surjectiveLift hσ =
      @Algebra.Extension.NaiveCotangent.Lift σ.source 𝒟.carrier _ _
        (𝒟.sourceAlgebra hσ) (@Algebra.Generators.toExtension σ.source 𝒟.carrier PEmpty.{u + 1} _ _ (𝒟.sourceAlgebra hσ) (𝒟.surjectiveGenerators hσ)) :=
  sorry

/-- Presentation homotopy from the canonical naive cotangent complex of
`A' → A` to the empty-generator complex. -/
def toSurjectiveHomotopy (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    HomotopyEquiv (𝒟.naiveCotangentOver hσ) (𝒟.surjectiveComplex hσ) :=
  @Algebra.Extension.NaiveCotangent.generatorsHomotopyEquiv σ.source 𝒟.carrier _ _
    (𝒟.sourceAlgebra hσ) _ _
    (@Algebra.Generators.self σ.source 𝒟.carrier _ _ (𝒟.sourceAlgebra hσ))
    (𝒟.surjectiveGenerators hσ)

/-- `toSurjectiveHomotopy` is `generatorsHomotopyEquiv` onto the empty-generator
presentation. -/
theorem toSurjectiveHomotopy_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.toSurjectiveHomotopy hσ =
      @Algebra.Extension.NaiveCotangent.generatorsHomotopyEquiv σ.source 𝒟.carrier _ _
    (𝒟.sourceAlgebra hσ) _ _
        (@Algebra.Generators.self σ.source 𝒟.carrier _ _ (𝒟.sourceAlgebra hσ))
        (𝒟.surjectiveGenerators hσ) :=
  sorry

private theorem toConormalHomotopy_laws (𝒟 : DualObstruction X)
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    Subsingleton ((𝒟.surjectiveComplex hσ).X 0) :=
  sorry

/-- Concentration homotopy of the empty-generator presentation onto the conormal
in chain-complex degree one. -/
def toConormalHomotopy (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    HomotopyEquiv (𝒟.surjectiveComplex hσ)
      ((HomologicalComplex.single (ModuleCat.{u} 𝒟.carrier) (down ℕ) 1).obj
        (𝒟.surjectiveLiftModule hσ)) :=
  @Algebra.Extension.NaiveCotangent.homotopyEquivSingleOneOfSubsingleton
    σ.source 𝒟.carrier _ _ (𝒟.sourceAlgebra hσ)
    (@Algebra.Generators.toExtension σ.source 𝒟.carrier PEmpty.{u + 1} _ _ (𝒟.sourceAlgebra hσ) (𝒟.surjectiveGenerators hσ))
    (by exact toConormalHomotopy_laws 𝒟 hσ)

/-- `toConormalHomotopy` is the subsingleton cotangent-space concentration. -/
theorem toConormalHomotopy_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.toConormalHomotopy hσ =
      @Algebra.Extension.NaiveCotangent.homotopyEquivSingleOneOfSubsingleton
    σ.source 𝒟.carrier _ _ (𝒟.sourceAlgebra hσ)
        (@Algebra.Generators.toExtension σ.source 𝒟.carrier PEmpty.{u + 1} _ _ (𝒟.sourceAlgebra hσ) (𝒟.surjectiveGenerators hσ))
        (by exact toConormalHomotopy_laws 𝒟 hσ) :=
  sorry

/-- The composite homotopy `NL{A⁄A'} ≃ I[1]` of a square-zero surjection. -/
def toKernelHomotopy (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    HomotopyEquiv (𝒟.naiveCotangentOver hσ)
      ((HomologicalComplex.single (ModuleCat.{u} 𝒟.carrier) (down ℕ) 1).obj
        (𝒟.surjectiveLiftModule hσ)) :=
  (𝒟.toSurjectiveHomotopy hσ).trans (𝒟.toConormalHomotopy hσ)

/-- `toKernelHomotopy` composes presentation independence with concentration. -/
theorem toKernelHomotopy_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.toKernelHomotopy hσ =
      (𝒟.toSurjectiveHomotopy hσ).trans (𝒟.toConormalHomotopy hσ) :=
  sorry

private theorem conormalToKernelLinear_laws (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    let v : 𝒟.surjectiveLift hσ → σ.source := fun l ↦ constantCoeff
      (Function.surjInv (@Algebra.Extension.Cotangent.mk_surjective σ.source 𝒟.carrier _ _
          (𝒟.sourceAlgebra hσ) (@Algebra.Generators.toExtension σ.source 𝒟.carrier PEmpty.{u + 1} _ _ (𝒟.sourceAlgebra hσ) (𝒟.surjectiveGenerators hσ)))
        ((@Algebra.Extension.NaiveCotangent.liftEquiv σ.source 𝒟.carrier _ _
          (𝒟.sourceAlgebra hσ) (@Algebra.Generators.toExtension σ.source 𝒟.carrier PEmpty.{u + 1} _ _ (𝒟.sourceAlgebra hσ) (𝒟.surjectiveGenerators hσ))) l)).1
    (∀ x, v x ∈ RingHom.ker (DeformationSituation.toCarrierOver hσ)) ∧
    (∀ (hm : ∀ x, v x ∈ RingHom.ker (DeformationSituation.toCarrierOver hσ)),
      (∀ x y, (⟨v (x + y), hm (x + y)⟩ : kernelModule (DeformationSituation.toCarrierOver hσ)) =
        ⟨v x, hm x⟩ + ⟨v y, hm y⟩) ∧
      (∀ (c : 𝒟.carrier) x, (⟨v (c • x), hm (c • x)⟩ : kernelModule (DeformationSituation.toCarrierOver hσ)) =
        c • (⟨v x, hm x⟩ : kernelModule (DeformationSituation.toCarrierOver hσ)))) :=
  sorry

/-- Linear comparison from the lifted conormal of the stored surjection to the
kernel of `toCarrierOver`, via `liftEquiv` and the square-zero identification
`I ⧸ I² ≃ I`. -/
def conormalToKernelLinear (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.surjectiveLift hσ →ₗ[𝒟.carrier]
      kernelModule (DeformationSituation.toCarrierOver hσ) :=
  { toFun := fun l ↦
      ⟨constantCoeff
          (Function.surjInv (@Algebra.Extension.Cotangent.mk_surjective σ.source 𝒟.carrier _ _
          (𝒟.sourceAlgebra hσ) (@Algebra.Generators.toExtension σ.source 𝒟.carrier PEmpty.{u + 1} _ _ (𝒟.sourceAlgebra hσ) (𝒟.surjectiveGenerators hσ)))
            ((@Algebra.Extension.NaiveCotangent.liftEquiv σ.source 𝒟.carrier _ _
      (𝒟.sourceAlgebra hσ)
                (@Algebra.Generators.toExtension σ.source 𝒟.carrier PEmpty.{u + 1} _ _ (𝒟.sourceAlgebra hσ) (𝒟.surjectiveGenerators hσ))) l)).1,
        (by exact (conormalToKernelLinear_laws 𝒟 hσ).1 _)⟩
    map_add' := by exact ((conormalToKernelLinear_laws 𝒟 hσ).2 (conormalToKernelLinear_laws 𝒟 hσ).1).1
    map_smul' := by exact ((conormalToKernelLinear_laws 𝒟 hσ).2 (conormalToKernelLinear_laws 𝒟 hσ).1).2 }

/-- `conormalToKernelLinear` evaluates a cotangent representative in the kernel
of `toCarrierOver`. -/
theorem conormalToKernelLinear_apply (𝒟 : DualObstruction X)
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec) (l : 𝒟.surjectiveLift hσ) :
    (𝒟.conormalToKernelLinear hσ l).1 =
      constantCoeff
        (Function.surjInv (@Algebra.Extension.Cotangent.mk_surjective σ.source 𝒟.carrier _ _
          (𝒟.sourceAlgebra hσ) (@Algebra.Generators.toExtension σ.source 𝒟.carrier PEmpty.{u + 1} _ _ (𝒟.sourceAlgebra hσ) (𝒟.surjectiveGenerators hσ)))
          ((@Algebra.Extension.NaiveCotangent.liftEquiv σ.source 𝒟.carrier _ _
      (𝒟.sourceAlgebra hσ)
              (@Algebra.Generators.toExtension σ.source 𝒟.carrier PEmpty.{u + 1} _ _ (𝒟.sourceAlgebra hσ) (𝒟.surjectiveGenerators hσ))) l)).1 :=
  sorry

/-- The square-zero comparison sends the class of every kernel representative
to its constant coefficient, independently of the representative selected by `surjInv`. -/
theorem conormalToKernelLinear_mk (𝒟 : DualObstruction X)
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    letI := 𝒟.sourceAlgebra hσ
    ∀ p : (𝒟.surjectiveGenerators hσ).toExtension.ker,
      (𝒟.conormalToKernelLinear hσ
        ((Algebra.Extension.NaiveCotangent.liftEquiv
          (𝒟.surjectiveGenerators hσ).toExtension).symm
            (Algebra.Extension.Cotangent.mk p))).1 = constantCoeff p.1 :=
  sorry

private theorem conormalToKernel_laws (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    let v : 𝒟.surjectiveLift hσ → σ.source := fun l ↦ (𝒟.conormalToKernelLinear hσ l).1
    (∀ x, v x ∈ RingHom.ker σ.toCarrier) ∧
    (∀ (hm : ∀ x, v x ∈ RingHom.ker σ.toCarrier),
      (∀ x y, (⟨v (x + y), hm (x + y)⟩ : DeformationSituation.kernelOver hσ) =
        ⟨v x, hm x⟩ + ⟨v y, hm y⟩) ∧
      (∀ (c : 𝒟.carrier) x, (⟨v (c • x), hm (c • x)⟩ : DeformationSituation.kernelOver hσ) =
        @SMul.smul 𝒟.carrier (DeformationSituation.kernelOver hσ)
          (DeformationSituation.kernelOver hσ).isModule.toSMul c ⟨v x, hm x⟩)) :=
  sorry

/-- The `A`-linear comparison from the concentrated conormal module to
`kernelOver`, identifying `ULift` of `Ideal.Cotangent (ker toCarrier)` with the
kernel since `(ker)² = 0`, transported along `liftEquiv`. -/
def conormalToKernel (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.surjectiveLiftModule hσ ⟶
      DeformationSituation.kernelOver hσ :=
  ConcreteCategory.ofHom
    { toFun := fun l ↦ ⟨(𝒟.conormalToKernelLinear hσ l).1, (by exact (conormalToKernel_laws 𝒟 hσ).1 _)⟩
      map_add' := by exact ((conormalToKernel_laws 𝒟 hσ).2 (conormalToKernel_laws 𝒟 hσ).1).1
      map_smul' := by exact ((conormalToKernel_laws 𝒟 hσ).2 (conormalToKernel_laws 𝒟 hσ).1).2 }

/-- `conormalToKernel` keeps the underlying kernel element of the square-zero
identification. -/
theorem conormalToKernel_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec)
    (l : 𝒟.surjectiveLift hσ) :
    (𝒟.conormalToKernel hσ l).1 = (𝒟.conormalToKernelLinear hσ l).1 :=
  sorry

/-- The derived morphism `NL{A⁄Λ} ⟶ I⟦1⟧` of a deformation situation over `𝒟`. -/
def toKernelShift (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier ⟶
      ((ModuleCat.single0 (DeformationSituation.kernelOver hσ))⟦(1 : ℤ)⟧) :=
  @Algebra.NaiveCotangent.naiveCotangentMap 𝒟.base σ.source 𝒟.carrier _ _ _
    (𝒟.sourceBaseAlgebra hσ) 𝒟.algebra (𝒟.sourceAlgHom hσ) ≫
    DerivedCategory.Q.map
      (extendMap (𝒟.toKernelHomotopy hσ).hom embeddingDownNat) ≫
    DerivedCategory.Q.map
      (extendSingleIso embeddingDownNat
        (𝒟.surjectiveLiftModule hσ)
        (1 : ℕ) (-1 : ℤ) rfl).hom ≫
    (DerivedCategory.singleFunctor (ModuleCat 𝒟.carrier) (-1)).map
      (𝒟.conormalToKernel hσ) ≫
    ((DerivedCategory.singleFunctors (ModuleCat 𝒟.carrier)).shiftIso
      (1 : ℤ) (-1) 0 (add_neg_cancel (1 : ℤ))).inv.app
      (DeformationSituation.kernelOver hσ)

/-- `toKernelShift` is `naiveCotangentMap` of `sourceAlgHom` followed by
concentration onto `I⟦1⟧`. -/
theorem toKernelShift_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.toKernelShift hσ =
      @Algebra.NaiveCotangent.naiveCotangentMap 𝒟.base σ.source 𝒟.carrier _ _ _
    (𝒟.sourceBaseAlgebra hσ) 𝒟.algebra (𝒟.sourceAlgHom hσ) ≫
        DerivedCategory.Q.map
          (extendMap (𝒟.toKernelHomotopy hσ).hom embeddingDownNat) ≫
        DerivedCategory.Q.map
          (extendSingleIso embeddingDownNat
            (𝒟.surjectiveLiftModule hσ)
            (1 : ℕ) (-1 : ℤ) rfl).hom ≫
        (DerivedCategory.singleFunctor (ModuleCat 𝒟.carrier) (-1)).map
          (𝒟.conormalToKernel hσ) ≫
        ((DerivedCategory.singleFunctors (ModuleCat 𝒟.carrier)).shiftIso
          (1 : ℤ) (-1) 0 (add_neg_cancel (1 : ℤ))).inv.app
          (DeformationSituation.kernelOver hσ) :=
  sorry

/-- Evaluation `ξ_{A'}` of a class in `H¹(K ⊗^L NL{A⁄Λ})` on a deformation
situation, along the stored square-zero thickening. -/
def evalExtension (𝒟 : DualObstruction X)
    (ξ : homologyTensorDerived 𝒟.complex 1
      (Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier))
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    (homologyTensor 𝒟.complex 2).obj (DeformationSituation.kernelOver hσ) :=
  ((DerivedCategory.homologyFunctor (ModuleCat 𝒟.carrier) 0).shiftIso
      (1 : ℤ) 1 2 rfl).hom.app
    ((DerivedCategory.derivedTensorProduct (DerivedCategory.Q.obj 𝒟.complex)).obj
      (ModuleCat.single0 (DeformationSituation.kernelOver hσ)))
    ((DerivedCategory.homologyFunctor (ModuleCat 𝒟.carrier) 1).map
      (((DerivedCategory.derivedTensorProduct
            (DerivedCategory.Q.obj 𝒟.complex)).map (𝒟.toKernelShift hσ)) ≫
        ((derivedTensorProduct_commShift
            (DerivedCategory.Q.obj 𝒟.complex)).commShiftIso (1 : ℤ)).hom.app
          (ModuleCat.single0 (DeformationSituation.kernelOver hσ)))
      ξ)

/-- `evalExtension` is homology of derived tensor with `toKernelShift`,
identified with `H²(K ⊗^L I)`. -/
theorem evalExtension_eq (𝒟 : DualObstruction X)
    (ξ : homologyTensorDerived 𝒟.complex 1
      (Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier))
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.evalExtension ξ hσ =
      ((DerivedCategory.homologyFunctor (ModuleCat 𝒟.carrier) 0).shiftIso
          (1 : ℤ) 1 2 rfl).hom.app
        ((DerivedCategory.derivedTensorProduct (DerivedCategory.Q.obj 𝒟.complex)).obj
          (ModuleCat.single0 (DeformationSituation.kernelOver hσ)))
        ((DerivedCategory.homologyFunctor (ModuleCat 𝒟.carrier) 1).map
          (((DerivedCategory.derivedTensorProduct
                (DerivedCategory.Q.obj 𝒟.complex)).map (𝒟.toKernelShift hσ)) ≫
            ((derivedTensorProduct_commShift
                (DerivedCategory.Q.obj 𝒟.complex)).commShiftIso (1 : ℤ)).hom.app
              (ModuleCat.single0 (DeformationSituation.kernelOver hσ)))
          ξ) :=
  sorry

/-- Evaluation `ξ_can` of a class in `H¹(K ⊗^L NL{A⁄Λ})` along `NL{A⁄Λ} ⟶ Ω{A⁄Λ}`. -/
def evalKaehler (𝒟 : DualObstruction X)
    (ξ : homologyTensorDerived 𝒟.complex 1
      (Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier)) :
    (homologyTensor 𝒟.complex 1).obj 𝒟.kaehler :=
  (DerivedCategory.homologyFunctor (ModuleCat 𝒟.carrier) 1).map
    ((DerivedCategory.derivedTensorProduct
        (DerivedCategory.Q.obj 𝒟.complex)).map 𝒟.toKaehler)
    ξ

/-- `evalKaehler` is homology of derived tensor with `toKaehler`. -/
theorem evalKaehler_eq (𝒟 : DualObstruction X)
    (ξ : homologyTensorDerived 𝒟.complex 1
      (Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier)) :
    𝒟.evalKaehler ξ =
      (DerivedCategory.homologyFunctor (ModuleCat 𝒟.carrier) 1).map
        ((DerivedCategory.derivedTensorProduct
            (DerivedCategory.Q.obj 𝒟.complex)).map 𝒟.toKaehler)
        ξ :=
  sorry

/-- The connecting map `∂ : H¹(K ⊗^L I₁) ⟶ H²(K ⊗^L I₃)` of a short exact
sequence of kernels. -/
def connecting (𝒟 : DualObstruction X) {sc : ShortComplex (ModuleCat.{u} 𝒟.carrier)}
    (hsc : sc.ShortExact) :
    (homologyTensor 𝒟.complex 1).obj sc.X₃ ⟶
      (homologyTensor 𝒟.complex 2).obj sc.X₁ :=
  DerivedCategory.HomologySequence.δ
    (CategoryTheory.Pretriangulated.Triangle.mk
      ((DerivedCategory.derivedTensorProduct
          (DerivedCategory.Q.obj 𝒟.complex)).map
        ((DerivedCategory.singleFunctor (ModuleCat 𝒟.carrier) 0).map sc.f))
      ((DerivedCategory.derivedTensorProduct
          (DerivedCategory.Q.obj 𝒟.complex)).map
        ((DerivedCategory.singleFunctor (ModuleCat 𝒟.carrier) 0).map sc.g))
      (((DerivedCategory.derivedTensorProduct
            (DerivedCategory.Q.obj 𝒟.complex)).map hsc.singleδ) ≫
        ((derivedTensorProduct_commShift
            (DerivedCategory.Q.obj 𝒟.complex)).commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (ModuleCat 𝒟.carrier) 0).obj sc.X₁)))
    1 2

/-- `connecting` is the homology connecting map of derived tensor with the
single triangle of the kernel sequence. -/
theorem connecting_eq (𝒟 : DualObstruction X)
    {sc : ShortComplex (ModuleCat.{u} 𝒟.carrier)} (hsc : sc.ShortExact) :
    𝒟.connecting hsc =
      DerivedCategory.HomologySequence.δ
        (CategoryTheory.Pretriangulated.Triangle.mk
          ((DerivedCategory.derivedTensorProduct
              (DerivedCategory.Q.obj 𝒟.complex)).map
            ((DerivedCategory.singleFunctor (ModuleCat 𝒟.carrier) 0).map sc.f))
          ((DerivedCategory.derivedTensorProduct
              (DerivedCategory.Q.obj 𝒟.complex)).map
            ((DerivedCategory.singleFunctor (ModuleCat 𝒟.carrier) 0).map sc.g))
          (((DerivedCategory.derivedTensorProduct
                (DerivedCategory.Q.obj 𝒟.complex)).map hsc.singleδ) ≫
            ((derivedTensorProduct_commShift
                (DerivedCategory.Q.obj 𝒟.complex)).commShiftIso (1 : ℤ)).hom.app
              ((DerivedCategory.singleFunctor (ModuleCat 𝒟.carrier) 0).obj sc.X₁)))
        1 2 :=
  sorry

/-- The kernel sequence `I₃ → I₂ → I₁` of a composable pair of morphisms of
deformation situations over `𝒟`. -/
def kernelShortComplex (𝒟 : DualObstruction X)
    {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32)) :
    ShortComplex (ModuleCat.{u} 𝒟.carrier) where
  X₁ := DeformationSituation.kernelOver h3
  X₂ := DeformationSituation.kernelOver h2
  X₃ := DeformationSituation.kernelOver h1
  f := DeformationSituation.kernelMapOver h3 h2 f32 hf32
  g := DeformationSituation.kernelMapOver h2 h1 f21 hf21
  zero := DeformationSituation.kernelMapOver_comp_eq_zero h1 h2 h3 f21 f32 hf21 hf32 hses

/-- `kernelShortComplex` is the kernel sequence of `f32` and `f21`. -/
theorem kernelShortComplex_eq (𝒟 : DualObstruction X)
    {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32)) :
    𝒟.kernelShortComplex h1 h2 h3 f21 f32 hf21 hf32 hses =
      ShortComplex.mk
        (DeformationSituation.kernelMapOver h3 h2 f32 hf32)
        (DeformationSituation.kernelMapOver h2 h1 f21 hf21)
        (DeformationSituation.kernelMapOver_comp_eq_zero h1 h2 h3 f21 f32 hf21 hf32 hses) :=
  sorry

/-- Canonical identification `A₁' ≃ A[I₁]` of the first thickening in a short
exact sequence of deformation situations over `𝒟`. -/
def firstThickenIso (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32)) :=
  trivSqZeroIso
    (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
    (DeformationSituation.sourceHomOver h3 h2 f32 hf32)

/-- `firstThickenIso` is `trivSqZeroIso` of the transported source maps. -/
theorem firstThickenIso_eq (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32)) :
    𝒟.firstThickenIso h1 h2 h3 f21 f32 hf21 hf32 hses =
      trivSqZeroIso
        (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
        (DeformationSituation.sourceHomOver h3 h2 f32 hf32) :=
  sorry

private theorem kernelOverHom_laws (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    let v : kernelModule (DeformationSituation.toCarrierOver hσ) → σ.source := fun i ↦ i.val
    (∀ x, v x ∈ RingHom.ker σ.toCarrier) ∧
    (∀ (hm : ∀ x, v x ∈ RingHom.ker σ.toCarrier),
      (∀ x y, (⟨v (x + y), hm (x + y)⟩ : DeformationSituation.kernelOver hσ) =
        ⟨v x, hm x⟩ + ⟨v y, hm y⟩) ∧
      (∀ (c : 𝒟.carrier) x, (⟨v (c • x), hm (c • x)⟩ : DeformationSituation.kernelOver hσ) =
        @SMul.smul 𝒟.carrier (DeformationSituation.kernelOver hσ)
          (DeformationSituation.kernelOver hσ).isModule.toSMul c ⟨v x, hm x⟩)) :=
  sorry

/-- The `A`-linear comparison from the kernel of `toCarrierOver` to `kernelOver`. -/
def kernelOverHom (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    ModuleCat.of 𝒟.carrier (kernelModule (DeformationSituation.toCarrierOver hσ)) ⟶
      DeformationSituation.kernelOver hσ :=
  ConcreteCategory.ofHom
    { toFun := fun i ↦ ⟨i.val, (by exact (kernelOverHom_laws 𝒟 hσ).1 _)⟩
      map_add' := by exact ((kernelOverHom_laws 𝒟 hσ).2 (kernelOverHom_laws 𝒟 hσ).1).1
      map_smul' := by exact ((kernelOverHom_laws 𝒟 hσ).2 (kernelOverHom_laws 𝒟 hσ).1).2 }

/-- `kernelOverHom` keeps the underlying kernel element. -/
theorem kernelOverHom_apply (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec)
    (i : kernelModule (DeformationSituation.toCarrierOver hσ)) :
    𝒟.kernelOverHom hσ i = ⟨i.val, (by exact (kernelOverHom_laws 𝒟 hσ).1 i)⟩ :=
  sorry

private theorem firstThickenToTrivial_laws (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32)) :
    let f := (𝒟.firstThickenIso h1 h2 h3 f21 f32 hf21 hf32 hses).toFun
    f 1 = 1 ∧ (∀ x y, f (x * y) = f x * f y) ∧
      f 0 = 0 ∧ (∀ x y, f (x + y) = f x + f y) :=
  sorry

/-- The first source ring maps to the trivial square-zero extension by the kernel
of its transported extension map. -/
def firstThickenToTrivial (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32)) :
    σ1.source →+* TrivSqZeroExt 𝒟.carrier
      (kernelModule (DeformationSituation.toCarrierOver h1)) where
  toFun := (𝒟.firstThickenIso h1 h2 h3 f21 f32 hf21 hf32 hses).toFun
  map_one' := by exact (firstThickenToTrivial_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses).1
  map_mul' := by exact (firstThickenToTrivial_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses).2.1
  map_zero' := by exact (firstThickenToTrivial_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses).2.2.1
  map_add' := by exact (firstThickenToTrivial_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses).2.2.2

/-- The first-thickening ring map has the underlying function of the canonical
trivial square-zero isomorphism. -/
theorem firstThickenToTrivial_eq (𝒟 : DualObstruction X)
    {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32)) :
    𝒟.firstThickenToTrivial h1 h2 h3 f21 f32 hf21 hf32 hses =
      { toFun := (𝒟.firstThickenIso h1 h2 h3 f21 f32 hf21 hf32 hses).toFun
        map_one' := by exact (firstThickenToTrivial_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses).1
        map_mul' := by exact (firstThickenToTrivial_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses).2.1
        map_zero' := by exact (firstThickenToTrivial_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses).2.2.1
        map_add' := by exact (firstThickenToTrivial_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses).2.2.2 } :=
  sorry

/-- Fibre of the restricted lift over `Spec(A₁')`. -/
def restrictedFiber (𝒟 : DualObstruction X) {σ1 σ2 : DeformationSituation X}
    (f21 : DeformationSituation.Hom σ2 σ1) (ℓ : DeformationSituation.ObjectLift σ2) :
    X.p.Fiber (Over.mk σ1.sourceToS) :=
  Fiber.mk <|
    @IsHomLift.codomain_eq _ _ _ _ X.p _ _ σ1.obj
      (DeformationSituation.ObjectLift.restrict f21 ℓ).obj'
      (DeformationSituation.thickening σ1)
      (DeformationSituation.ObjectLift.restrict f21 ℓ).hom
      (DeformationSituation.ObjectLift.restrict f21 ℓ).isHomLift

/-- `restrictedFiber` is the fibre point of the restricted lift. -/
theorem restrictedFiber_eq (𝒟 : DualObstruction X) {σ1 σ2 : DeformationSituation X}
    (f21 : DeformationSituation.Hom σ2 σ1) (ℓ : DeformationSituation.ObjectLift σ2) :
    𝒟.restrictedFiber f21 ℓ =
      Fiber.mk
        (@IsHomLift.codomain_eq _ _ _ _ X.p _ _ σ1.obj
          (DeformationSituation.ObjectLift.restrict f21 ℓ).obj'
          (DeformationSituation.thickening σ1)
          (DeformationSituation.ObjectLift.restrict f21 ℓ).hom
          (DeformationSituation.ObjectLift.restrict f21 ℓ).isHomLift) :=
  sorry

private theorem firstThickenSpecHom_laws (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32)) :
    Spec.map (CommRingCat.ofHom
      (𝒟.firstThickenToTrivial h1 h2 h3 f21 f32 hf21 hf32 hses)) ≫ σ1.sourceToS =
      specTrivSqZero 𝒟.toS (ModuleCat.of 𝒟.carrier (kernelModule (DeformationSituation.toCarrierOver h1))) :=
  sorry

/-- The `Over S` morphism `Spec(A[I₁]) ⟶ Spec(A₁')` of `firstThickenToTrivial`. -/
def firstThickenSpecHom (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32)) :
    Over.mk (specTrivSqZero 𝒟.toS
        (ModuleCat.of 𝒟.carrier
          (kernelModule (DeformationSituation.toCarrierOver h1)))) ⟶
      Over.mk σ1.sourceToS :=
  specOverHom
    (CommRingCat.ofHom (𝒟.firstThickenToTrivial h1 h2 h3 f21 f32 hf21 hf32 hses))
    (by exact firstThickenSpecHom_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses)

/-- `firstThickenSpecHom` is `specOverHom` of `firstThickenToTrivial`. -/
theorem firstThickenSpecHom_eq (𝒟 : DualObstruction X)
    {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32)) :
    𝒟.firstThickenSpecHom h1 h2 h3 f21 f32 hf21 hf32 hses =
      specOverHom
        (CommRingCat.ofHom (𝒟.firstThickenToTrivial h1 h2 h3 f21 f32 hf21 hf32 hses))
        (by exact firstThickenSpecHom_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses) :=
  sorry

private theorem liftToTrivialHom_laws (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32))
    (ℓ : DeformationSituation.ObjectLift σ2) :
    X.p.IsHomLift
      ((specOverHom
      (trivSqZeroHom (CommRingCat.of 𝒟.carrier) (ModuleCat.of 𝒟.carrier (kernelModule (DeformationSituation.toCarrierOver h1))))
      (trivSqZeroHom_comp 𝒟.toS (ModuleCat.of 𝒟.carrier (kernelModule (DeformationSituation.toCarrierOver h1))))) ≫ 𝒟.firstThickenSpecHom h1 h2 h3 f21 f32 hf21 hf32 hses)
      (eqToHom (congrArg ObjectOverSpec.obj h1).symm ≫
        (DeformationSituation.ObjectLift.restrict f21 ℓ).hom) :=
  sorry

/-- The total morphism of the restricted lift after `A₁' ≃ A[I₁]`. -/
def liftToTrivialHom (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32))
    (ℓ : DeformationSituation.ObjectLift σ2) :
    𝒟.obj ⟶
      (Chosen.reindexObj X.p
        (𝒟.firstThickenSpecHom h1 h2 h3 f21 f32 hf21 hf32 hses)
        (𝒟.restrictedFiber f21 ℓ)).1 :=
  FiberedCategoryOver.Groupoids.cartesianFactorOf X.p
    (𝒟.firstThickenSpecHom h1 h2 h3 f21 f32 hf21 hf32 hses)
    (specOverHom
      (trivSqZeroHom (CommRingCat.of 𝒟.carrier)
              (ModuleCat.of 𝒟.carrier
                (kernelModule (DeformationSituation.toCarrierOver h1))))
      (trivSqZeroHom_comp 𝒟.toS
              (ModuleCat.of 𝒟.carrier
                (kernelModule (DeformationSituation.toCarrierOver h1)))))
    (𝒟.restrictedFiber f21 ℓ)
    (eqToHom (congrArg ObjectOverSpec.obj h1).symm ≫
      (DeformationSituation.ObjectLift.restrict f21 ℓ).hom)
    (by exact liftToTrivialHom_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses ℓ)

/-- `liftToTrivialHom` is the cartesian factor of the restricted lift. -/
theorem liftToTrivialHom_eq (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32))
    (ℓ : DeformationSituation.ObjectLift σ2) :
    𝒟.liftToTrivialHom h1 h2 h3 f21 f32 hf21 hf32 hses ℓ =
      FiberedCategoryOver.Groupoids.cartesianFactorOf X.p
        (𝒟.firstThickenSpecHom h1 h2 h3 f21 f32 hf21 hf32 hses)
        (specOverHom
          (trivSqZeroHom (CommRingCat.of 𝒟.carrier)
              (ModuleCat.of 𝒟.carrier
                (kernelModule (DeformationSituation.toCarrierOver h1))))
          (trivSqZeroHom_comp 𝒟.toS
              (ModuleCat.of 𝒟.carrier
                (kernelModule (DeformationSituation.toCarrierOver h1)))))
        (𝒟.restrictedFiber f21 ℓ)
        (eqToHom (congrArg ObjectOverSpec.obj h1).symm ≫
          (DeformationSituation.ObjectLift.restrict f21 ℓ).hom)
        (by exact liftToTrivialHom_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses ℓ) :=
  sorry

private theorem liftClass_laws (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32))
    (ℓ : DeformationSituation.ObjectLift σ2) :
    X.p.IsHomLift (specOverHom
      (trivSqZeroHom (CommRingCat.of 𝒟.carrier) (ModuleCat.of 𝒟.carrier (kernelModule (DeformationSituation.toCarrierOver h1))))
      (trivSqZeroHom_comp 𝒟.toS (ModuleCat.of 𝒟.carrier (kernelModule (DeformationSituation.toCarrierOver h1)))))
      (𝒟.liftToTrivialHom h1 h2 h3 f21 f32 hf21 hf32 hses ℓ) :=
  sorry

/-- The `H¹`-class attached to a lift of the first thickening after identifying
`A₁' ≃ A[I₁]`. -/
def liftClass (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32))
    (ℓ : DeformationSituation.ObjectLift σ2) :
    (homologyTensor 𝒟.complex 1).obj (DeformationSituation.kernelOver h1) :=
  (homologyTensor 𝒟.complex 1).map (𝒟.kernelOverHom h1) (
      ULift.down
    (𝒟.tangentIso.hom.app (ModuleCat.of 𝒟.carrier (kernelModule (DeformationSituation.toCarrierOver h1)))
      ((tangentForget (Spectrum.ObjectOverSpec.toFiber 𝒟.toObjectOverSpec)
          (ModuleCat.of 𝒟.carrier (kernelModule (DeformationSituation.toCarrierOver h1)))).symm
        (lifts.mk
          (@UnderLift.ofHom _ _ _ _ X.p _ _ _
            (Spectrum.ObjectOverSpec.toFiber 𝒟.toObjectOverSpec) _
            (𝒟.liftToTrivialHom h1 h2 h3 f21 f32 hf21 hf32 hses ℓ)
            (by exact liftClass_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses ℓ))))))

/-- `liftClass` is the `H¹` image of the restricted lift after `A₁' ≃ A[I₁]`
and `T_x ≅ H¹(K ⊗^L -)`. -/
theorem liftClass_eq (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32))
    (ℓ : DeformationSituation.ObjectLift σ2) :
    𝒟.liftClass h1 h2 h3 f21 f32 hf21 hf32 hses ℓ =
      (homologyTensor 𝒟.complex 1).map (𝒟.kernelOverHom h1) (
      ULift.down
        (𝒟.tangentIso.hom.app (ModuleCat.of 𝒟.carrier (kernelModule (DeformationSituation.toCarrierOver h1)))
          ((tangentForget (Spectrum.ObjectOverSpec.toFiber 𝒟.toObjectOverSpec)
              (ModuleCat.of 𝒟.carrier (kernelModule (DeformationSituation.toCarrierOver h1)))).symm
            (lifts.mk
              (@UnderLift.ofHom _ _ _ _ X.p _ _ _
                (Spectrum.ObjectOverSpec.toFiber 𝒟.toObjectOverSpec) _
                (𝒟.liftToTrivialHom h1 h2 h3 f21 f32 hf21 hf32 hses ℓ)
                (by exact liftClass_laws 𝒟 h1 h2 h3 f21 f32 hf21 hf32 hses ℓ)))))) :=
  sorry

/-- Compatibility of obstruction classes with the connecting map of a short
exact sequence of deformation situations. -/
def IsConnectingCompatible (𝒟 : DualObstruction X) : Prop :=
  ∀ {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hrest21 : f21.restriction = DeformationSituation.objHomIdOver h2 h1)
    (hrest32 : f32.restriction = DeformationSituation.objHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32))
    (hker : (𝒟.kernelShortComplex h1 h2 h3 f21 f32 hf21 hf32 hses).ShortExact)
    (ℓ : DeformationSituation.ObjectLift σ2),
    𝒟.obstruction h3 =
      𝒟.connecting hker (𝒟.liftClass h1 h2 h3 f21 f32 hf21 hf32 hses ℓ)

/-- Connecting compatibility is the identity `o_x(A₃') = ∂θ` for the `H¹`-class
`θ` of the restricted middle lift, after `A₁' ≃ A[I₁]` and `T_x ≅ H¹`. -/
theorem IsConnectingCompatible_iff (𝒟 : DualObstruction X) :
    IsConnectingCompatible 𝒟 ↔
      ∀ {σ1 σ2 σ3 : DeformationSituation X}
        (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
        (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
        (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
        (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
        (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
        (hrest21 : f21.restriction = DeformationSituation.objHomIdOver h2 h1)
        (hrest32 : f32.restriction = DeformationSituation.objHomIdOver h3 h2)
        (hses : AlgebraicGeometry.Deformation.IsShortExact
          (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
          (DeformationSituation.sourceHomOver h3 h2 f32 hf32))
        (hker : (𝒟.kernelShortComplex h1 h2 h3 f21 f32 hf21 hf32 hses).ShortExact)
        (ℓ : DeformationSituation.ObjectLift σ2),
        𝒟.obstruction h3 =
          𝒟.connecting hker (𝒟.liftClass h1 h2 h3 f21 f32 hf21 hf32 hses ℓ) :=
  sorry

/-- A class in `H¹(K ⊗^L NL{A⁄Λ})` recovers every obstruction `o_x(A')` along
the canonical geometric tower `Λ → A' → A` of a deformation situation over `𝒟`. -/
def RecoversObstructions (𝒟 : DualObstruction X)
    (ξ : homologyTensorDerived 𝒟.complex 1
      (Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier)) : Prop :=
  ∀ (σ : DeformationSituation X) (hσ : σ.IsOver 𝒟.toObjectOverSpec),
    𝒟.evalExtension ξ hσ = 𝒟.obstruction hσ

/-- `RecoversObstructions` is the identity `ξ_{A'} = o_x(A')` for every
deformation situation over `𝒟`, using the constructed `sourceAlgHom`. -/
theorem recoversObstructions_iff (𝒟 : DualObstruction X)
    (ξ : homologyTensorDerived 𝒟.complex 1
      (Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier)) :
    RecoversObstructions 𝒟 ξ ↔
      ∀ (σ : DeformationSituation X) (hσ : σ.IsOver 𝒟.toObjectOverSpec),
        𝒟.evalExtension ξ hσ = 𝒟.obstruction hσ :=
  sorry

end DualObstruction

end AlgebraicGeometry.GroupoidsOver
