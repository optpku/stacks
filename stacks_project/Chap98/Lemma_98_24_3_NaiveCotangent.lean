module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.Extension.Cotangent.Surjective
public import stacks_project.Chap98.Lemma_98_21_1
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import stacks_project.Chap98.Lemma_98_23_2_Comparison
public import stacks_project.Chap98.Remark_98_21_5_Thickening
public import stacks_project.Chap98.Remark_98_21_8_Canonical_element_Lift
public import stacks_project.Chap98.Situation_98_24_2_DualObstruction

/-!
# Naive cotangent evaluations of dual obstruction classes

Evaluation of a class in `H¹(K ⊗^L NL{A⁄Λ})` along `NL{A⁄Λ} ⟶ I⟦1⟧` and
along `NL{A⁄Λ} ⟶ Ω{A⁄Λ}`, together with the connecting map of a short exact
sequence of kernels and the compatibility hypothesis (iv).
-/

@[expose] public section

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

/-- Transport of `A' → A` to a square-zero map into the carrier of a fixed
object `ξ` over `Spec(A)`. -/
def toCarrierOver {σ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) : σ.source →+* ξ.carrier where
  toFun a' :=
    cast (congrArg ObjectOverSpec.carrier hσ) (σ.toCarrier a')
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- `toCarrierOver` applies the stored square-zero map and casts the codomain
along `IsOver`. -/
theorem toCarrierOver_apply {σ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (a' : σ.source) :
    toCarrierOver hσ a' =
      cast (congrArg ObjectOverSpec.carrier hσ) (σ.toCarrier a') :=
  sorry

/-- `toCarrierOver hσ` remains a square-zero extension. -/
instance toCarrierOver_isSquareZero {σ : DeformationSituation X}
    {ξ : ObjectOverSpec X} (hσ : σ.IsOver ξ) :
    (toCarrierOver hσ).IsSquareZeroExtension :=
  sorry

/-- The source ring map of a morphism of deformation situations, as a morphism
of square-zero extensions of the carrier of `ξ`. -/
def sourceHomOver {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) (f : Hom σ τ)
    (hf : f.toRingHom = ringHomIdOver hσ hτ) :
    AlgebraicGeometry.Deformation.Hom (toCarrierOver hσ) (toCarrierOver hτ) :=
  AlgebraicGeometry.Deformation.Hom.of f.toSourceHom sorry

/-- `sourceHomOver` has underlying source map `f.toSourceHom`. -/
theorem sourceHomOver_hom {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) (f : Hom σ τ)
    (hf : f.toRingHom = ringHomIdOver hσ hτ) :
    (sourceHomOver hσ hτ f hf).hom = f.toSourceHom :=
  sorry

/-- The object of `X` obtained by reindexing a lift along a source ring map. -/
def ObjectLift.reindexObj {σ τ : DeformationSituation X} (f : Hom σ τ)
    (ℓ : ObjectLift σ) : X.total :=
  (Chosen.reindexObj X.p
    (specOverHom (CommRingCat.ofHom f.toSourceHom) f.sourceToS_comp)
    (Fiber.mk <|
      @IsHomLift.codomain_eq _ _ _ _ X.p _ _ σ.obj ℓ.obj' (thickening σ) ℓ.hom
        ℓ.isHomLift)).1

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
      (f.restriction ≫ ℓ.hom) sorry)
    sorry

/-- The restricted lift is obtained by cartesian reindexing of the original
lifted object. -/
theorem ObjectLift.restrict_obj' {σ τ : DeformationSituation X} (f : Hom σ τ)
    (ℓ : ObjectLift σ) :
    (ObjectLift.restrict f ℓ).obj' = ObjectLift.reindexObj f ℓ :=
  sorry

/-- Convert an object lift into an isomorphism class in `Lift(x, A')`. -/
def ObjectLift.toLifts {σ : DeformationSituation X} (ℓ : ObjectLift σ) :
    lifts (toFiber σ.toObjectOverSpec) (CommRingCat.ofHom σ.toCarrier) σ.toS_comp :=
  lifts.mk <|
    @UnderLift.ofHom _ _ _ _ X.p _ _
      (specOverHom (CommRingCat.ofHom σ.toCarrier) σ.toS_comp)
      (toFiber σ.toObjectOverSpec) ℓ.obj' ℓ.hom sorry

/-- `ObjectLift.toLifts` is the class of the packaged under-lift. -/
theorem ObjectLift.toLifts_eq {σ : DeformationSituation X} (ℓ : ObjectLift σ) :
    ObjectLift.toLifts ℓ =
      lifts.mk
        (@UnderLift.ofHom _ _ _ _ X.p _ _
          (specOverHom (CommRingCat.ofHom σ.toCarrier) σ.toS_comp)
          (toFiber σ.toObjectOverSpec) ℓ.obj' ℓ.hom sorry) :=
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
  kaehlerObj 𝒟.baseHom

/-- `kaehler` is `kaehlerObj` of `baseHom`. -/
theorem kaehler_eq (𝒟 : DualObstruction X) :
    𝒟.kaehler = kaehlerObj 𝒟.baseHom :=
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

/-- The Λ-algebra map `A' → A` of a deformation situation over `𝒟`, for the
supplied `Λ`-algebra structure on `A'`. Prefer `evalExtension`, which
instantiates this at `sourceBaseAlgebra`. -/
def sourceAlgHom (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) [Algebra 𝒟.base σ.source] :
    σ.source →ₐ[𝒟.base] 𝒟.carrier where
  toRingHom := DeformationSituation.toCarrierOver hσ
  commutes' := sorry

/-- `sourceAlgHom` is `toCarrierOver` as a `Λ`-algebra map. -/
theorem sourceAlgHom_toRingHom (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) [Algebra 𝒟.base σ.source] :
    (𝒟.sourceAlgHom hσ).toRingHom = DeformationSituation.toCarrierOver hσ :=
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
  -- Local instance justification (noncanonical choice): the Λ-algebra structure
  -- on A' is the unique factorization of sourceToS through Spec(Λ).
  letI : Algebra 𝒟.base σ.source := 𝒟.sourceBaseAlgebra hσ
  IsScalarTower.of_algHom (𝒟.sourceAlgHom hσ)

/-- `sourceTower` is `IsScalarTower.of_algHom` of `sourceAlgHom`. -/
theorem sourceTower_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.sourceTower hσ =
      -- Local instance justification (noncanonical choice): the Λ-algebra structure
      -- on A' is the unique factorization of sourceToS through Spec(Λ).
      letI : Algebra 𝒟.base σ.source := 𝒟.sourceBaseAlgebra hσ
      IsScalarTower.of_algHom (𝒟.sourceAlgHom hσ) :=
  sorry

/-- The universal derivation of `kaehler` as a `Λ`-derivation on `A`. -/
def kaehlerDerivation (𝒟 : DualObstruction X) :
    Derivation 𝒟.base 𝒟.carrier (𝒟.kaehler : Type u) :=
  { toLinearMap :=
      { toFun := kaehlerD 𝒟.baseHom
        map_add' := sorry
        map_smul' := sorry }
    map_one_eq_zero' := sorry
    leibniz' := sorry }

/-- `kaehlerDerivation` evaluates as `kaehlerD`. -/
theorem kaehlerDerivation_apply (𝒟 : DualObstruction X) (a : 𝒟.carrier) :
    𝒟.kaehlerDerivation a = kaehlerD 𝒟.baseHom a :=
  sorry

/-- The canonical chain map `NL{A⁄Λ} ⟶ Ω{A⁄Λ}[0]`. -/
def toKaehlerChain (𝒟 : DualObstruction X) :
    Algebra.naiveCotangent 𝒟.base 𝒟.carrier ⟶
      (ChainComplex.single₀ (ModuleCat.{u} 𝒟.carrier)).obj 𝒟.kaehler :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ConcreteCategory.ofHom
      { toFun := fun x ↦
          ((Algebra.Generators.self 𝒟.base 𝒟.carrier).cotangentSpaceBasis.repr x).sum
            fun a c ↦ c • 𝒟.kaehlerDerivation a
        map_add' := sorry
        map_smul' := sorry },
      sorry⟩

/-- `toKaehlerChain` is the unique chain map induced by `toKaehler` in degree
zero. -/
theorem toKaehlerChain_eq (𝒟 : DualObstruction X) :
    𝒟.toKaehlerChain =
      (ChainComplex.toSingle₀Equiv _ _).symm
        ⟨ConcreteCategory.ofHom
          { toFun := fun x ↦
              ((Algebra.Generators.self 𝒟.base 𝒟.carrier).cotangentSpaceBasis.repr x).sum
                fun a c ↦ c • 𝒟.kaehlerDerivation a
            map_add' := sorry
            map_smul' := sorry },
          sorry⟩ :=
  sorry

/-- Comparison of the unbundled Kähler module `Ω{A⁄Λ}` with `kaehlerObj` of the
bundled algebra map `baseHom`. -/
def kaehlerCompare (𝒟 : DualObstruction X) :
    ModuleCat.of 𝒟.carrier Ω[𝒟.carrier ⁄ 𝒟.base] ⟶ 𝒟.kaehler :=
  ConcreteCategory.ofHom
    { toFun := fun ω ↦
        @KaehlerDifferential.map 𝒟.base 𝒟.base 𝒟.baseCommRing 𝒟.baseCommRing
          (Algebra.id 𝒟.base) 𝒟.carrier 𝒟.carrier 𝒟.commRing 𝒟.commRing 𝒟.algebra
          (Algebra.id 𝒟.carrier) 𝒟.baseHom.hom.toAlgebra 𝒟.baseHom.hom.toAlgebra
          (sorry : @IsScalarTower 𝒟.base 𝒟.carrier 𝒟.carrier 𝒟.algebra.toSMul
            (Algebra.id 𝒟.carrier).toSMul 𝒟.baseHom.hom.toAlgebra.toSMul)
          (sorry : @IsScalarTower 𝒟.base 𝒟.base 𝒟.carrier (Algebra.id 𝒟.base).toSMul
            𝒟.baseHom.hom.toAlgebra.toSMul 𝒟.baseHom.hom.toAlgebra.toSMul)
          (sorry : @SMulCommClass 𝒟.base 𝒟.carrier 𝒟.carrier
            𝒟.baseHom.hom.toAlgebra.toSMul (Algebra.id 𝒟.carrier).toSMul)
          ω
      map_add' := sorry
      map_smul' := sorry }

/-- The self-presentation augmentation `d ≫ toKaehler` vanishes. -/
theorem toKaehler_comp_d (𝒟 : DualObstruction X) :
    (Algebra.naiveCotangent 𝒟.base 𝒟.carrier).d 1 0 ≫
      ModuleCat.ofHom
        (Algebra.Generators.self 𝒟.base 𝒟.carrier).toExtension.toKaehler = 0 :=
  sorry

/-- The derived morphism `NL{A⁄Λ} ⟶ Ω{A⁄Λ}` in `D(A)`, as the self-presentation
augmentation `Extension.toKaehler` transported to `kaehlerObj`. -/
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
  sorry

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
  -- Local instance justification (noncanonical choice): the `A'`-algebra
  -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
  letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
  Algebra.Extension.NaiveCotangent.complex (𝒟.surjectiveGenerators hσ).toExtension

/-- `surjectiveComplex` is the presentation complex of `surjectiveGenerators`. -/
theorem surjectiveComplex_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.surjectiveComplex hσ =
      -- Local instance justification (noncanonical choice): the `A'`-algebra
      -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
      letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
      Algebra.Extension.NaiveCotangent.complex (𝒟.surjectiveGenerators hσ).toExtension :=
  sorry

/-- The lifted conormal module of `surjectiveGenerators`. -/
abbrev surjectiveLift (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) : Type u :=
  -- Local instance justification (noncanonical choice): the `A'`-algebra
  -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
  letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
  Algebra.Extension.NaiveCotangent.Lift (𝒟.surjectiveGenerators hσ).toExtension

/-- `surjectiveLift` is `NaiveCotangent.Lift` of `surjectiveGenerators`. -/
theorem surjectiveLift_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.surjectiveLift hσ =
      -- Local instance justification (noncanonical choice): the `A'`-algebra
      -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
      letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
      Algebra.Extension.NaiveCotangent.Lift (𝒟.surjectiveGenerators hσ).toExtension :=
  sorry

/-- The `A`-module structure on the lifted conormal of the stored square-zero
surjection. -/
instance instModule_surjectiveLift (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    Module 𝒟.carrier (𝒟.surjectiveLift hσ) :=
  -- Local instance justification (noncanonical choice): the `A'`-algebra
  -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
  letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
  inferInstance

/-- Presentation homotopy from the canonical naive cotangent complex of
`A' → A` to the empty-generator complex. -/
def toSurjectiveHomotopy (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    HomotopyEquiv (𝒟.naiveCotangentOver hσ) (𝒟.surjectiveComplex hσ) :=
  -- Local instance justification (noncanonical choice): the `A'`-algebra
  -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
  letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
  Algebra.Extension.NaiveCotangent.generatorsHomotopyEquiv
    (Algebra.Generators.self σ.source 𝒟.carrier)
    (𝒟.surjectiveGenerators hσ)

/-- `toSurjectiveHomotopy` is `generatorsHomotopyEquiv` onto the empty-generator
presentation. -/
theorem toSurjectiveHomotopy_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.toSurjectiveHomotopy hσ =
      -- Local instance justification (noncanonical choice): the `A'`-algebra
      -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
      letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
      Algebra.Extension.NaiveCotangent.generatorsHomotopyEquiv
        (Algebra.Generators.self σ.source 𝒟.carrier)
        (𝒟.surjectiveGenerators hσ) :=
  sorry

/-- Concentration homotopy of the empty-generator presentation onto the conormal
in chain-complex degree one. -/
def toConormalHomotopy (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    HomotopyEquiv (𝒟.surjectiveComplex hσ)
      ((HomologicalComplex.single (ModuleCat.{u} 𝒟.carrier) (down ℕ) 1).obj
        (ModuleCat.of 𝒟.carrier (𝒟.surjectiveLift hσ))) :=
  -- Local instance justification (noncanonical choice): the `A'`-algebra
  -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
  letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
  Algebra.Extension.NaiveCotangent.homotopyEquivSingleOneOfSubsingleton
    (𝒟.surjectiveGenerators hσ).toExtension
    (Subsingleton.intro fun _ _ ↦ sorry)

/-- `toConormalHomotopy` is the subsingleton cotangent-space concentration. -/
theorem toConormalHomotopy_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.toConormalHomotopy hσ =
      -- Local instance justification (noncanonical choice): the `A'`-algebra
      -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
      letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
      Algebra.Extension.NaiveCotangent.homotopyEquivSingleOneOfSubsingleton
        (𝒟.surjectiveGenerators hσ).toExtension
        (Subsingleton.intro fun _ _ ↦ sorry) :=
  sorry

/-- The composite homotopy `NL{A⁄A'} ≃ I[1]` of a square-zero surjection. -/
def toKernelHomotopy (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    HomotopyEquiv (𝒟.naiveCotangentOver hσ)
      ((HomologicalComplex.single (ModuleCat.{u} 𝒟.carrier) (down ℕ) 1).obj
        (ModuleCat.of 𝒟.carrier (𝒟.surjectiveLift hσ))) :=
  (𝒟.toSurjectiveHomotopy hσ).trans (𝒟.toConormalHomotopy hσ)

/-- `toKernelHomotopy` composes presentation independence with concentration. -/
theorem toKernelHomotopy_eq (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.toKernelHomotopy hσ =
      (𝒟.toSurjectiveHomotopy hσ).trans (𝒟.toConormalHomotopy hσ) :=
  sorry

/-- Linear comparison from the lifted conormal of the stored surjection to the
kernel of `toCarrierOver`, via `liftEquiv` and the square-zero identification
`I ⧸ I² ≃ I`. -/
def conormalToKernelLinear (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.surjectiveLift hσ →ₗ[𝒟.carrier]
      kernelModule (DeformationSituation.toCarrierOver hσ) :=
  -- Local instance justification (noncanonical choice): the `A'`-algebra
  -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
  letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
  { toFun := fun l ↦
      ⟨constantCoeff
          (Function.surjInv Algebra.Extension.Cotangent.mk_surjective
            ((Algebra.Extension.NaiveCotangent.liftEquiv
                (𝒟.surjectiveGenerators hσ).toExtension) l)).1,
        sorry⟩
    map_add' := sorry
    map_smul' := sorry }

/-- `conormalToKernelLinear` evaluates a cotangent representative in the kernel
of `toCarrierOver`. -/
theorem conormalToKernelLinear_apply (𝒟 : DualObstruction X)
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec) (l : 𝒟.surjectiveLift hσ) :
    (𝒟.conormalToKernelLinear hσ l).1 =
      -- Local instance justification (noncanonical choice): the `A'`-algebra
      -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
      letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
      constantCoeff
        (Function.surjInv Algebra.Extension.Cotangent.mk_surjective
          ((Algebra.Extension.NaiveCotangent.liftEquiv
              (𝒟.surjectiveGenerators hσ).toExtension) l)).1 :=
  sorry

/-- The `A`-linear comparison from the concentrated conormal module to
`kernelOver`, identifying `ULift` of `Ideal.Cotangent (ker toCarrier)` with the
kernel since `(ker)² = 0`, transported along `liftEquiv`. -/
def conormalToKernel (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    ModuleCat.of 𝒟.carrier (𝒟.surjectiveLift hσ) ⟶
      DeformationSituation.kernelOver hσ :=
  ConcreteCategory.ofHom
    { toFun := fun l ↦ ⟨(𝒟.conormalToKernelLinear hσ l).1, sorry⟩
      map_add' := sorry
      map_smul' := sorry }

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
  -- Local instance justification (noncanonical choice): the Λ-algebra structure
  -- on A' is the unique factorization of sourceToS through Spec(Λ).
  letI : Algebra 𝒟.base σ.source := 𝒟.sourceBaseAlgebra hσ
  -- Local instance justification (noncanonical choice): the `A'`-algebra
  -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
  letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
  -- Local instance justification (noncanonical choice): the tower `Λ → A' → A`
  -- is induced by `sourceAlgHom`.
  letI : IsScalarTower 𝒟.base σ.source 𝒟.carrier := 𝒟.sourceTower hσ
  Algebra.NaiveCotangent.naiveCotangentMap (𝒟.sourceAlgHom hσ) ≫
    DerivedCategory.Q.map
      (extendMap (𝒟.toKernelHomotopy hσ).hom embeddingDownNat) ≫
    DerivedCategory.Q.map
      (extendSingleIso embeddingDownNat
        (ModuleCat.of 𝒟.carrier (𝒟.surjectiveLift hσ))
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
      -- Local instance justification (noncanonical choice): the Λ-algebra structure
      -- on A' is the unique factorization of sourceToS through Spec(Λ).
      letI : Algebra 𝒟.base σ.source := 𝒟.sourceBaseAlgebra hσ
      -- Local instance justification (noncanonical choice): the `A'`-algebra
      -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
      letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
      Algebra.NaiveCotangent.naiveCotangentMap (𝒟.sourceAlgHom hσ) ≫
        DerivedCategory.Q.map
          (extendMap (𝒟.toKernelHomotopy hσ).hom embeddingDownNat) ≫
        DerivedCategory.Q.map
          (extendSingleIso embeddingDownNat
            (ModuleCat.of 𝒟.carrier (𝒟.surjectiveLift hσ))
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
  -- Local instance justification (noncanonical choice): the Λ-algebra structure
  -- on A' is the unique factorization of sourceToS through Spec(Λ).
  letI : Algebra 𝒟.base σ.source := 𝒟.sourceBaseAlgebra hσ
  -- Local instance justification (noncanonical choice): the `A'`-algebra
  -- structure on `A` is the stored square-zero surjection `toCarrierOver`.
  letI : Algebra σ.source 𝒟.carrier := 𝒟.sourceAlgebra hσ
  -- Local instance justification (noncanonical choice): the tower `Λ → A' → A`
  -- is induced by `sourceAlgHom`.
  letI : IsScalarTower 𝒟.base σ.source 𝒟.carrier := 𝒟.sourceTower hσ
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
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2) :
    ShortComplex (ModuleCat.{u} 𝒟.carrier) where
  X₁ := DeformationSituation.kernelOver h3
  X₂ := DeformationSituation.kernelOver h2
  X₃ := DeformationSituation.kernelOver h1
  f := DeformationSituation.kernelMapOver h3 h2 f32 hf32
  g := DeformationSituation.kernelMapOver h2 h1 f21 hf21
  zero := sorry

/-- `kernelShortComplex` is the kernel sequence of `f32` and `f21`. -/
theorem kernelShortComplex_eq (𝒟 : DualObstruction X)
    {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2) :
    𝒟.kernelShortComplex h1 h2 h3 f21 f32 hf21 hf32 =
      ShortComplex.mk
        (DeformationSituation.kernelMapOver h3 h2 f32 hf32)
        (DeformationSituation.kernelMapOver h2 h1 f21 hf21) sorry :=
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

/-- The `A`-linear comparison from the kernel of `toCarrierOver` to `kernelOver`. -/
def kernelOverHom (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    ModuleCat.of 𝒟.carrier (kernelModule (DeformationSituation.toCarrierOver hσ)) ⟶
      DeformationSituation.kernelOver hσ :=
  ConcreteCategory.ofHom
    { toFun := fun i ↦ ⟨i.val, sorry⟩
      map_add' := sorry
      map_smul' := sorry }

/-- `kernelOverHom` keeps the underlying kernel element. -/
theorem kernelOverHom_apply (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec)
    (i : kernelModule (DeformationSituation.toCarrierOver hσ)) :
    𝒟.kernelOverHom hσ i = ⟨i.val, sorry⟩ :=
  sorry

/-- The ring map `A₁' → A[I₁]` landing in `TrivSqZeroExt` of `kernelOver`. -/
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
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- `firstThickenToTrivial` is `trivSqZeroIso` followed by `TrivSqZeroExt.map`. -/
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
        map_one' := sorry
        map_mul' := sorry
        map_zero' := sorry
        map_add' := sorry } :=
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
    sorry

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
        sorry :=
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
    sorry

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
        sorry :=
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
  ULift.down
    (𝒟.tangentIso.hom.app (DeformationSituation.kernelOver h1)
      ((tangentForget (toFiber 𝒟.toObjectOverSpec)
          (DeformationSituation.kernelOver h1)).symm
        (lifts.mk
          (@UnderLift.ofHom _ _ _ _ X.p _ _ _
            (toFiber 𝒟.toObjectOverSpec) _
            (𝒟.liftToTrivialHom h1 h2 h3 f21 f32 hf21 hf32 hses ℓ)
            sorry))))

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
      ULift.down
        (𝒟.tangentIso.hom.app (DeformationSituation.kernelOver h1)
          ((tangentForget (toFiber 𝒟.toObjectOverSpec)
              (DeformationSituation.kernelOver h1)).symm
            (lifts.mk
              (@UnderLift.ofHom _ _ _ _ X.p _ _ _
                (toFiber 𝒟.toObjectOverSpec) _
                (𝒟.liftToTrivialHom h1 h2 h3 f21 f32 hf21 hf32 hses ℓ)
                sorry)))) :=
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
    (hker : (𝒟.kernelShortComplex h1 h2 h3 f21 f32 hf21 hf32).ShortExact)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32))
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
        (hker : (𝒟.kernelShortComplex h1 h2 h3 f21 f32 hf21 hf32).ShortExact)
        (hses : AlgebraicGeometry.Deformation.IsShortExact
          (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
          (DeformationSituation.sourceHomOver h3 h2 f32 hf32))
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
