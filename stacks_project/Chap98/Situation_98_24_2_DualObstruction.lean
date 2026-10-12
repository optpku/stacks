/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import stacks_project.Chap98.Definition_98_22_1_DeformationSituation
public import stacks_project.Chap98.Lemma_98_21_2_Functor

/-!
# Dual obstruction data at a finite-type object

On a locally Noetherian base, extra data at one finite-type object `x` over
`Spec(A)`: a complex `K` of `A`-modules, an identification of `T_x` with
`H^1(K ⊗^L_A -)`, and obstruction classes in `H^2(K ⊗^L_A I)` for deformation
situations of this `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {A : Type u} [CommRing A]

/-- The functor sending `M` to the `n`-th homology of the derived tensor of `M`
with `K`. The source spelling `H^n(K ⊗^L_A M)` is `homologyTensor_comm`. -/
def homologyTensor (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  ModuleCat.single0Functor ⋙
    DerivedCategory.derivedTensorProduct (DerivedCategory.Q.obj K) ⋙
    DerivedCategory.homologyFunctor (ModuleCat A) n

/-- The value of `homologyTensor K n` on `M` is the `n`-th homology of the
derived tensor of `K` with `M` in degree zero. -/
theorem homologyTensor_obj (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (M : ModuleCat.{u} A) :
    (homologyTensor K n).obj M =
      (DerivedCategory.homologyFunctor (ModuleCat A) n).obj
        ((DerivedCategory.derivedTensorProduct (DerivedCategory.Q.obj K)).obj
          (ModuleCat.single0 M)) :=
  sorry

/-- Comparison of `homologyTensor` with the swapped derived-tensor spelling
`H^n((single0 M) ⊗^L K)` used for obstruction modules in Example 98.24.1. -/
def homologyTensor_comm (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (M : ModuleCat.{u} A) :
    (homologyTensor K n).obj M ≅
      (DerivedCategory.homologyFunctor (ModuleCat A) n).obj
        ((DerivedCategory.derivedTensorProduct (ModuleCat.single0 M)).obj
          (DerivedCategory.Q.obj K)) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) n).mapIso
    (DerivedCategory.derivedTensorProduct_comm (DerivedCategory.Q.obj K)
      (ModuleCat.single0 M)).symm

/-- Universe lift of `homologyTensor K n` to `ModuleCat.{u+1}`, matching the
landing universe of `tangentFunctor`. -/
def homologyTensorUlift (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u + 1} A :=
  homologyTensor K n ⋙ ModuleCat.uliftFunctor.{u + 1, u} A

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- The fibre object of `x` over `Spec(A) ⟶ S`. -/
def toFiber {X : GroupoidsOver S} (ξ : ObjectOverSpec X) :
    X.p.Fiber (Over.mk ξ.toS) :=
  Functor.Fiber.mk ξ.over_obj

/-- `toFiber ξ` is the fibre point associated to `ξ.over_obj`. -/
theorem toFiber_eq_mk {X : GroupoidsOver S} (ξ : ObjectOverSpec X) :
    toFiber ξ = Functor.Fiber.mk ξ.over_obj :=
  sorry

namespace DeformationSituation

variable {X : GroupoidsOver S}

/-- A deformation situation lies over a fixed object `ξ` when it has the same
`Spec(A)`, structure map, and object `x`. -/
def IsOver (σ : DeformationSituation X) (ξ : ObjectOverSpec X) : Prop :=
  σ.toObjectOverSpec = ξ

/-- `IsOver` is equality of the underlying objects over spectra. -/
theorem isOver_iff (σ : DeformationSituation X) (ξ : ObjectOverSpec X) :
    σ.IsOver ξ ↔ σ.toObjectOverSpec = ξ :=
  sorry

/-- Carrier identification `σ.carrier = ξ.carrier` when `σ` lies over `ξ`. -/
theorem carrier_eq {σ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) : σ.carrier = ξ.carrier :=
  sorry

/-- The kernel `I = Ker(A' → A)` as an `A`-module on the carrier of `ξ`. -/
def kernelOver {σ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) : ModuleCat.{u} ξ.carrier :=
  @ModuleCat.of ξ.carrier inferInstance (RingHom.ker σ.toCarrier) inferInstance
    (Eq.recOn (motive := fun (η : ObjectOverSpec X) (_h : σ.toObjectOverSpec = η) ↦
        Module η.carrier (RingHom.ker σ.toCarrier))
      hσ (inferInstance : Module σ.carrier (RingHom.ker σ.toCarrier)))

/-- Identity `A → A` transported to `σ.carrier →+* τ.carrier` when both
situations lie over the same `ξ`. -/
def ringHomIdOver {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) : σ.carrier →+* τ.carrier where
  toFun := fun a ↦
    cast (congrArg ObjectOverSpec.carrier hτ).symm
      (cast (congrArg ObjectOverSpec.carrier hσ) a)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Identity arrow on `x`, transported to `τ.obj ⟶ σ.obj` when both situations
lie over the same `ξ`. -/
def objHomIdOver {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) : τ.obj ⟶ σ.obj :=
  eqToHom ((congrArg ObjectOverSpec.obj hτ).trans (congrArg ObjectOverSpec.obj hσ).symm)

/-- The map `I → I'` on kernels over a common object `ξ`, induced by a morphism
of deformation situations that is the identity on `A`. -/
def kernelMapOver {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) (f : Hom σ τ)
    (hf : f.toRingHom = ringHomIdOver hσ hτ) :
    kernelOver hσ ⟶ kernelOver hτ :=
  ConcreteCategory.ofHom
    { toFun := fun i ↦ ⟨f.toSourceHom i.1, Hom.kernelMap_mem f i⟩
      map_add' := sorry
      map_smul' := sorry }

/-- `kernelMapOver` sends a kernel element to its image under the source ring
map. -/
theorem kernelMapOver_apply {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) (f : Hom σ τ)
    (hf : f.toRingHom = ringHomIdOver hσ hτ) (i : kernelOver hσ) :
    kernelMapOver hσ hτ f hf i = ⟨f.toSourceHom i.1, Hom.kernelMap_mem f i⟩ :=
  sorry

end DeformationSituation

variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

/-- Dual obstruction data at a single finite-type object `x` over `Spec(A)`,
factoring through an affine open `Spec(Λ)`: a complex `K` of `A`-modules, an
isomorphism `T_x ≅ H^1(K ⊗^L_A -)`, and obstruction classes
`o_x(A') ∈ H^2(K ⊗^L_A I)` for deformation situations of this `x`. -/
structure DualObstruction (X : GroupoidsOver S) [HasStrongRimSchlessinger X]
    extends ObjectOverSpec X where
  /-- `Spec(A) ⟶ S` is locally of finite type. -/
  [locallyOfFiniteType : LocallyOfFiniteType toS]
  /-- The coefficient ring `Λ` of the affine open. -/
  base : Type u
  [baseCommRing : CommRing base]
  /-- Open immersion `Spec(Λ) ⟶ S`. -/
  openImmersion : Spec (CommRingCat.of base) ⟶ S
  [isOpenImmersion : IsOpenImmersion openImmersion]
  [algebra : Algebra base carrier]
  /-- The structure map factors as `Spec(A) ⟶ Spec(Λ) ⟶ S`. -/
  factor :
    Spec.map (CommRingCat.ofHom (algebraMap base carrier)) ≫ openImmersion = toS
  /-- The complex `K` of `A`-modules. -/
  complex : CochainComplex (ModuleCat.{u} carrier) ℤ
  /-- Isomorphism `T_x(-) ≅ H^1(K ⊗^L_A -)` after the universe lift of
  homology. -/
  tangentIso :
    tangentFunctor (toFiber toObjectOverSpec) ≅ homologyTensorUlift complex 1
  /-- Obstruction class `o_x(A') ∈ H^2(K ⊗^L_A I)` of a deformation situation
  of this `x`. -/
  obstruction : {σ : DeformationSituation X} → (hσ : σ.IsOver toObjectOverSpec) →
    (homologyTensor complex 2).obj (DeformationSituation.kernelOver hσ)
  /-- Obstruction classes are natural along morphisms of deformation situations
  that fix `A` and `x`. -/
  map_obstruction : ∀ {σ τ : DeformationSituation X}
      (hσ : σ.IsOver toObjectOverSpec) (hτ : τ.IsOver toObjectOverSpec)
      (f : DeformationSituation.Hom σ τ)
      (hf : f.toRingHom = DeformationSituation.ringHomIdOver hσ hτ),
    f.restriction = DeformationSituation.objHomIdOver hσ hτ →
      (homologyTensor complex 2).map
          (DeformationSituation.kernelMapOver hσ hτ f hf) (obstruction hσ) =
        obstruction hτ
  /-- `x` lifts to `Spec(A')` if and only if the obstruction vanishes. -/
  lifts_iff : ∀ {σ : DeformationSituation X} (hσ : σ.IsOver toObjectOverSpec),
    Nonempty (DeformationSituation.ObjectLift σ) ↔ obstruction hσ = 0

attribute [instance] DualObstruction.locallyOfFiniteType
attribute [instance] DualObstruction.baseCommRing
attribute [instance] DualObstruction.isOpenImmersion
attribute [instance] DualObstruction.algebra

namespace DualObstruction

/-- Package a finite-type object over `Spec(A)` through `Spec(Λ)`, a complex,
a tangent comparison, and obstruction classes as dual obstruction data; the
naturality and lifting laws are deferred. -/
def of (ξ : ObjectOverSpec X) [LocallyOfFiniteType ξ.toS]
    (base : Type u) [CommRing base]
    (openImmersion : Spec (CommRingCat.of base) ⟶ S) [IsOpenImmersion openImmersion]
    [Algebra base ξ.carrier]
    (factor :
      Spec.map (CommRingCat.ofHom (algebraMap base ξ.carrier)) ≫ openImmersion = ξ.toS)
    (complex : CochainComplex (ModuleCat.{u} ξ.carrier) ℤ)
    (tangentIso : tangentFunctor (toFiber ξ) ≅ homologyTensorUlift complex 1)
    (obstruction : {σ : DeformationSituation X} → (hσ : σ.IsOver ξ) →
      (homologyTensor complex 2).obj (DeformationSituation.kernelOver hσ)) :
    DualObstruction X where
  toObjectOverSpec := ξ
  base := base
  openImmersion := openImmersion
  factor := factor
  complex := complex
  tangentIso := tangentIso
  obstruction := obstruction
  map_obstruction := sorry
  lifts_iff := sorry

/-- Dual obstruction data records finite type of `Spec(A) ⟶ S`, a factorization
through an affine open `Spec(Λ)`, an isomorphism `T_x ≅ H^1(K ⊗^L_A -)`,
natural obstruction classes, and the lifting criterion. -/
theorem spec (𝒟 : DualObstruction X) :
    LocallyOfFiniteType 𝒟.toS ∧
      (Spec.map (CommRingCat.ofHom (algebraMap 𝒟.base 𝒟.carrier)) ≫
          𝒟.openImmersion = 𝒟.toS) ∧
      IsIso 𝒟.tangentIso.hom ∧
      (∀ {σ τ : DeformationSituation X}
          (hσ : σ.IsOver 𝒟.toObjectOverSpec) (hτ : τ.IsOver 𝒟.toObjectOverSpec)
          (f : DeformationSituation.Hom σ τ)
          (hf : f.toRingHom = DeformationSituation.ringHomIdOver hσ hτ),
        f.restriction = DeformationSituation.objHomIdOver hσ hτ →
          (homologyTensor 𝒟.complex 2).map
              (DeformationSituation.kernelMapOver hσ hτ f hf) (𝒟.obstruction hσ) =
            𝒟.obstruction hτ) ∧
      ∀ {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec),
        Nonempty (DeformationSituation.ObjectLift σ) ↔ 𝒟.obstruction hσ = 0 :=
  sorry

/-- The derived object of the stored complex in `D(A)`. -/
def derivedObject (𝒟 : DualObstruction X) :
    DerivedCategory (ModuleCat 𝒟.carrier) :=
  DerivedCategory.Q.obj 𝒟.complex

/-- `derivedObject` is the image of the stored complex under `Q`. -/
theorem derivedObject_eq (𝒟 : DualObstruction X) :
    𝒟.derivedObject = DerivedCategory.Q.obj 𝒟.complex :=
  sorry

/-- The obstruction of a deformation situation of this `x` vanishes if and only
if there is a lift of `x` along `Spec(A) ⟶ Spec(A')`. -/
theorem obstruction_eq_zero_iff_nonempty_objectLift (𝒟 : DualObstruction X)
    {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec) :
    𝒟.obstruction hσ = 0 ↔ Nonempty (DeformationSituation.ObjectLift σ) :=
  sorry

end DualObstruction

end AlgebraicGeometry.GroupoidsOver
