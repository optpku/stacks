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
public import ReasLib.AlgebraicGeometry.GroupoidsOver.DualObstruction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.DeformationSituation.FixedObject
public import stacks_project.Chap98.Situation_98_24_2_DualObstruction

public import ReasLib.AlgebraicGeometry.GroupoidsOver.DualObstruction.NaiveCotangent

/-!
# Naive cotangent evaluations of dual obstruction classes

Typed compatibility checks for cotangent evaluation, lift restriction, and
connecting compatibility. The source imports retain the canonical-element and
fibre accessors used by downstream source statements.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open HomologicalComplex ComplexShape AlgebraicGeometry.Deformation
open CategoryTheory.Pretriangulated
open MvPolynomial AlgebraicGeometry.GroupoidsOver
open scoped NaiveCotangent

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

/- Situation 98.24.2: cotangent evaluation and connecting compatibility. -/
#check (AlgebraicGeometry.GroupoidsOver.homologyTensorDerived :
  ∀ (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (X : DerivedCategory (ModuleCat.{u} A)),
    ModuleCat.{u} A)

#check (AlgebraicGeometry.GroupoidsOver.DeformationSituation.ObjectLift.reindexObj :
  ∀ {σ τ : DeformationSituation X} (f : DeformationSituation.Hom σ τ)
    (ℓ : DeformationSituation.ObjectLift σ),
    X.total)

#check (AlgebraicGeometry.GroupoidsOver.DeformationSituation.ObjectLift.restrict :
  ∀ {σ τ : DeformationSituation X} (f : DeformationSituation.Hom σ τ)
    (ℓ : DeformationSituation.ObjectLift σ),
    DeformationSituation.ObjectLift τ)

#check (AlgebraicGeometry.GroupoidsOver.DeformationSituation.ObjectLift.toLifts :
  ∀ {σ : DeformationSituation X} (ℓ : DeformationSituation.ObjectLift σ),
    lifts (toFiber σ.toObjectOverSpec) (CommRingCat.ofHom σ.toCarrier) σ.toS_comp)

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.baseHom :
  ∀ (𝒟 : DualObstruction X),
    CommRingCat.of 𝒟.base ⟶ CommRingCat.of 𝒟.carrier)

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.kaehler :
  ∀ (𝒟 : DualObstruction X),
    ModuleCat.{u} 𝒟.carrier)

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.sourceBaseHom :
  ∀ (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec),
    𝒟.base →+* σ.source)

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.sourceAlgHom :
  ∀ (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec),
    @AlgHom 𝒟.base σ.source 𝒟.carrier _ _ _ (𝒟.sourceBaseAlgebra hσ) 𝒟.algebra)

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.kaehlerDerivation :
  ∀ (𝒟 : DualObstruction X),
    𝒟.kaehler.Derivation 𝒟.baseHom)

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.toKaehler :
  ∀ (𝒟 : DualObstruction X),
    Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier ⟶ ModuleCat.single0 𝒟.kaehler)

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.toKernelShift :
  ∀ (𝒟 : DualObstruction X) {σ : DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec),
    Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier ⟶
      ((ModuleCat.single0 (DeformationSituation.kernelOver hσ))⟦(1 : ℤ)⟧))

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.evalExtension :
  ∀ (𝒟 : DualObstruction X)
    (ξ : homologyTensorDerived 𝒟.complex 1
      (Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier))
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec),
    (homologyTensor 𝒟.complex 2).obj (DeformationSituation.kernelOver hσ))

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.evalKaehler :
  ∀ (𝒟 : DualObstruction X)
    (ξ : homologyTensorDerived 𝒟.complex 1
      (Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier)),
    (homologyTensor 𝒟.complex 1).obj 𝒟.kaehler)

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.connecting :
  ∀ (𝒟 : DualObstruction X) {sc : ShortComplex (ModuleCat.{u} 𝒟.carrier)}
    (hsc : sc.ShortExact),
    (homologyTensor 𝒟.complex 1).obj sc.X₃ ⟶
      (homologyTensor 𝒟.complex 2).obj sc.X₁)

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.kernelShortComplex :
  ∀ (𝒟 : DualObstruction X)
    {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32)),
    ShortComplex (ModuleCat.{u} 𝒟.carrier))

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.liftClass :
  ∀ (𝒟 : DualObstruction X) {σ1 σ2 σ3 : DeformationSituation X}
    (h1 : σ1.IsOver 𝒟.toObjectOverSpec) (h2 : σ2.IsOver 𝒟.toObjectOverSpec)
    (h3 : σ3.IsOver 𝒟.toObjectOverSpec)
    (f21 : DeformationSituation.Hom σ2 σ1) (f32 : DeformationSituation.Hom σ3 σ2)
    (hf21 : f21.toRingHom = DeformationSituation.ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = DeformationSituation.ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (DeformationSituation.sourceHomOver h2 h1 f21 hf21)
      (DeformationSituation.sourceHomOver h3 h2 f32 hf32))
    (ℓ : DeformationSituation.ObjectLift σ2),
    (homologyTensor 𝒟.complex 1).obj (DeformationSituation.kernelOver h1))

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.IsConnectingCompatible :
  ∀ (𝒟 : DualObstruction X),
    Prop)

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.IsConnectingCompatible_iff :
  ∀ (𝒟 : DualObstruction X),
    DualObstruction.IsConnectingCompatible 𝒟 ↔
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
          𝒟.connecting hker (𝒟.liftClass h1 h2 h3 f21 f32 hf21 hf32 hses ℓ))

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.RecoversObstructions :
  ∀ (𝒟 : DualObstruction X)
    (ξ : homologyTensorDerived 𝒟.complex 1
      (Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier)),
    Prop)

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.recoversObstructions_iff :
  ∀ (𝒟 : DualObstruction X)
    (ξ : homologyTensorDerived 𝒟.complex 1
      (Algebra.naiveCotangentObject 𝒟.base 𝒟.carrier)),
    DualObstruction.RecoversObstructions 𝒟 ξ ↔
      ∀ (σ : DeformationSituation X) (hσ : σ.IsOver 𝒟.toObjectOverSpec),
        𝒟.evalExtension ξ hσ = 𝒟.obstruction hσ)

