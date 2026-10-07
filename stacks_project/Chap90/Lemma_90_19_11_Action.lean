module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import stacks_project.Chap90.Lemma_90_19_7_Comparison
public import stacks_project.Chap90.Lemma_90_19_9_Module
public import stacks_project.Chap90.«90_17_5_1_Comparison»

/-!
# Free transitive Aut-fibre action of `Inf_{x0}(F) ⊗[k] I`

If `p` is cofibered in groupoids and satisfies (RS), and `φ : x' ⟶ x` lies over a
surjection `f : A' ⟶ A` whose kernel `I` is annihilated by `m_{A'}`, the composite
of the automorphism-functor (RS) comparison, `selfPullbackIso`, and the square-zero
pullback yields an action of the identity fibre of `autFunctor` at `k[I]` on
`Inf(x'/x)`. Transporting along the tensor comparison identifies the acting group
with `Inf_{x0}(F) ⊗[k] I`.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Limits
open Functor Fiber Chosen ArtinianLocalAlgCat IsLocalRing
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} [HasRimSchlessinger p]
variable {A' A : ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

variable (f : A' ⟶ A)
variable (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)

/-- The identity object `A' → A'` of `Under (p.obj x')`. -/
def infAutIdUnder (x' : p.Fiber A') : Under (p.obj (fiberInclusion.obj x')) :=
  Under.mk (𝟙 (p.obj (fiberInclusion.obj x')))

/-- The object `A' → A` of `Under (p.obj x')` associated to `f`. -/
def infAutBaseUnder (x' : p.Fiber A') : Under (p.obj (fiberInclusion.obj x')) :=
  Under.mk (eqToHom x'.property ≫ f)

/-- The object `A' → A' ×_A A'` of `Under (p.obj x')`, via the diagonal. -/
def infAutSelfPullbackUnder (x' : p.Fiber A') :
    Under (p.obj (fiberInclusion.obj x')) :=
  Under.mk (eqToHom x'.property ≫ selfPullbackDiagonal f)

/-- The object `A' → A' ×_k k[I]` of `Under (p.obj x')`, via the canonical section. -/
def infAutSquareZeroPullbackUnder (x' : p.Fiber A') :
    Under (p.obj (fiberInclusion.obj x')) :=
  Under.mk (eqToHom x'.property ≫ squareZeroPullbackSection A' (kerModule f hI))

/-- The object `A' → k[I]` of `Under (p.obj x')`. -/
def infAutSquareZeroUnder (x' : p.Fiber A') :
    Under (p.obj (fiberInclusion.obj x')) :=
  Under.mk (toResidue (p.obj (fiberInclusion.obj x')) ≫ residueToSquareZero (kerModule f hI))

/-- The restriction `(A' → A') ⟶ (A' → A)` in `Under (p.obj x')`. -/
def infAutIdToBase (x' : p.Fiber A') :
    infAutIdUnder x' ⟶ infAutBaseUnder f x' :=
  Under.homMk (eqToHom x'.property ≫ f) sorry

/-- The first projection `(A' → A' ×_A A') ⟶ (A' → A')` in `Under (p.obj x')`. -/
def infAutSelfPullbackFstUnder (x' : p.Fiber A') :
    infAutSelfPullbackUnder f x' ⟶ infAutIdUnder x' :=
  Under.homMk (selfPullbackFst f ≫ eqToHom x'.property.symm) sorry

/-- The second projection `(A' → A' ×_A A') ⟶ (A' → A')` in `Under (p.obj x')`. -/
def infAutSelfPullbackSndUnder (x' : p.Fiber A') :
    infAutSelfPullbackUnder f x' ⟶ infAutIdUnder x' :=
  Under.homMk (selfPullbackSnd f ≫ eqToHom x'.property.symm) sorry

/-- The structure map `(A' → A' ×_A A') ⟶ (A' → A)` in `Under (p.obj x')`. -/
def infAutSelfPullbackToBase (x' : p.Fiber A') :
    infAutSelfPullbackUnder f x' ⟶ infAutBaseUnder f x' :=
  Under.homMk (selfPullbackToBase f) sorry

/-- The first projection `(A' → A' ×_k k[I]) ⟶ (A' → A')` in `Under (p.obj x')`. -/
def infAutSquareZeroPullbackFstUnder (x' : p.Fiber A') :
    infAutSquareZeroPullbackUnder f hI x' ⟶ infAutIdUnder x' :=
  Under.homMk (squareZeroPullbackFst A' (kerModule f hI) ≫ eqToHom x'.property.symm) sorry

/-- The second projection `(A' → A' ×_k k[I]) ⟶ (A' → k[I])` in `Under (p.obj x')`. -/
def infAutSquareZeroPullbackSndUnder (x' : p.Fiber A') :
    infAutSquareZeroPullbackUnder f hI x' ⟶ infAutSquareZeroUnder f hI x' :=
  Under.homMk (squareZeroPullbackSnd A' (kerModule f hI)) sorry

/-- The restriction `(A' → k[I]) ⟶ (A' → k)` in `Under (p.obj x')`. -/
def infAutSquareZeroToResidueUnder (x' : p.Fiber A') :
    infAutSquareZeroUnder f hI x' ⟶ residueUnder (p.obj (fiberInclusion.obj x')) :=
  Under.homMk (squareZeroToResidue Λ k (kerModule f hI)) sorry

/-- The Under-isomorphism `A' ×_A A' ≅ A' ×_k k[I]` induced by `selfPullbackIso`. -/
def infAutSelfPullbackIsoUnder (x' : p.Fiber A') :
    infAutSelfPullbackUnder f x' ≅ infAutSquareZeroPullbackUnder f hI x' :=
  Under.isoMk (selfPullbackIso f hI) sorry

/-- The self-product square of `f` in `Under (p.obj x')` is a pullback. -/
theorem isPullback_infAutSelfPullbackUnder (x' : p.Fiber A') :
    IsPullback (infAutSelfPullbackFstUnder f x') (infAutSelfPullbackSndUnder f x')
      (infAutIdToBase f x') (infAutIdToBase f x') := sorry

/-- The underlying algebra map of `infAutIdToBase` is surjective. -/
theorem infAutIdToBase_surjective (hf : Function.Surjective f.hom) (x' : p.Fiber A') :
    Function.Surjective (infAutIdToBase f x').right.hom := sorry

/-- Identity fibre of `autFunctor p x` along an under-morphism. -/
def autIdFiber (x : F) {U V : Under (p.obj x)} (φ : U ⟶ V) :
    Subgroup (Aut (pushforwardObj p U.hom (ofObj p x))) where
  carrier :=
    {α | pushforwardAut p φ (ofObj p x) α =
      (1 : Aut (pushforwardObj p V.hom (ofObj p x)))}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

/-- Membership in `autIdFiber` is the identity-fibre condition for `pushforwardAut`. -/
theorem mem_autIdFiber (x : F) {U V : Under (p.obj x)} (φ : U ⟶ V)
    (α : Aut (pushforwardObj p U.hom (ofObj p x))) :
    α ∈ autIdFiber x φ ↔
      pushforwardAut p φ (ofObj p x) α =
        (1 : Aut (pushforwardObj p V.hom (ofObj p x))) := sorry

/-- Identity fibre of `autFunctor` along `A' → k[I] ⟶ k`, as `Lift(id, k[I])`. -/
def idAutSquareZero (x' : p.Fiber A') :
    Subgroup
      (Aut (pushforwardObj p (infAutSquareZeroUnder f hI x').hom
        (ofObj p (fiberInclusion.obj x')))) :=
  autIdFiber (fiberInclusion.obj x') (infAutSquareZeroToResidueUnder f hI x')

/-- Membership in `idAutSquareZero` is the identity-fibre condition along
`infAutSquareZeroToResidueUnder`. -/
theorem mem_idAutSquareZero (x' : p.Fiber A')
    (α : Aut (pushforwardObj p (infAutSquareZeroUnder f hI x').hom
      (ofObj p (fiberInclusion.obj x')))) :
    α ∈ idAutSquareZero f hI x' ↔
      α ∈ autIdFiber (fiberInclusion.obj x') (infAutSquareZeroToResidueUnder f hI x') :=
  sorry

/-- Addition on `idAutSquareZero` is composition in `Aut`. -/
instance instAdd_idAutSquareZero (x' : p.Fiber A') :
    Add (idAutSquareZero f hI x') where
  add α β := α * β

/-- Zero in `idAutSquareZero` is the identity automorphism. -/
instance instZero_idAutSquareZero (x' : p.Fiber A') :
    Zero (idAutSquareZero f hI x') where
  zero := 1

/-- Negation on `idAutSquareZero` is inversion in `Aut`. -/
instance instNeg_idAutSquareZero (x' : p.Fiber A') :
    Neg (idAutSquareZero f hI x') where
  neg α := α⁻¹

/-- The Under-endomorphism of `A' → k[I]` induced by scaling `I` by `r`. -/
def infAutSquareZeroSMulUnder (x' : p.Fiber A') (r : k) :
    infAutSquareZeroUnder f hI x' ⟶ infAutSquareZeroUnder f hI x' :=
  Under.homMk (squareZeroMap (r • (LinearMap.id : kerModule f hI →ₗ[k] kerModule f hI))) sorry

/-- Scalar multiplication on `idAutSquareZero` by square-zero scaling of `I`. -/
def idAutSquareZeroSMul (x' : p.Fiber A') (r : k)
    (α : idAutSquareZero f hI x') : idAutSquareZero f hI x' :=
  ⟨pushforwardAut p (infAutSquareZeroSMulUnder f hI x' r)
      (ofObj p (fiberInclusion.obj x')) α.val, sorry⟩

/-- Scalar multiplication on `idAutSquareZero`. -/
instance instSMul_idAutSquareZero (x' : p.Fiber A') :
    SMul k (idAutSquareZero f hI x') where
  smul := idAutSquareZeroSMul f hI x'

/-- The additive group structure on the identity fibre of `autFunctor` at `k[I]`. -/
instance instAddCommGroup_idAutSquareZero (x' : p.Fiber A') :
    AddCommGroup (idAutSquareZero f hI x') where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The `k`-module structure on the identity fibre of `autFunctor` at `k[I]`. -/
instance instModule_idAutSquareZero (x' : p.Fiber A') :
    Module k (idAutSquareZero f hI x') where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The Under-morphism `(A' → k[ε]) ⟶ (A' → k[I])` induced by `span{v}`. -/
def infAutSpanUnder (x' : p.Fiber A') (v : kerModule f hI) :
    dualNumberUnder (p.obj (fiberInclusion.obj x')) ⟶ infAutSquareZeroUnder f hI x' :=
  Under.homMk
    ((dualNumberIsoSquareZero Λ k).hom ≫
      squareZeroMap (LinearMap.toSpanSingleton k (kerModule f hI) v))
    sorry

/-- The bilinear comparison sending `(α, v)` to the image of `α` under
`autFunctor.map` of `infAutSpanUnder v`. -/
def idAutSquareZeroTensorBilin (x' : p.Fiber A') :
    idTangentSpace p (fiberInclusion.obj x') →ₗ[k]
      kerModule f hI →ₗ[k] idAutSquareZero f hI x' :=
  LinearMap.mk₂ k
    (fun α v ↦
      ⟨pushforwardAut p (infAutSpanUnder f hI x' v)
          (ofObj p (fiberInclusion.obj x')) α.val, sorry⟩)
    sorry sorry sorry sorry

/-- On pure tensors, `idAutSquareZeroTensorBilin` applies `pushforwardAut` of
`infAutSpanUnder v`. -/
theorem idAutSquareZeroTensorBilin_apply (x' : p.Fiber A')
    (α : idTangentSpace p (fiberInclusion.obj x')) (v : kerModule f hI) :
    (idAutSquareZeroTensorBilin f hI x' α v).val =
      pushforwardAut p (infAutSpanUnder f hI x' v)
        (ofObj p (fiberInclusion.obj x')) α.val := sorry

/-- Canonical `k`-linear identification of `Lift(id, k[I])` with
`T_id Aut(x') ⊗[k] I`. -/
def idAutSquareZeroTensor (x' : p.Fiber A') :
    idAutSquareZero f hI x' ≃ₗ[k]
      idTangentSpace p (fiberInclusion.obj x') ⊗[k] kerModule f hI :=
  (LinearEquiv.ofBijective (TensorProduct.lift (idAutSquareZeroTensorBilin f hI x')) sorry).symm

/-- The underlying linear map of `idAutSquareZeroTensor` is the inverse of
`TensorProduct.lift` of `idAutSquareZeroTensorBilin`. -/
theorem idAutSquareZeroTensor_spec (x' : p.Fiber A')
    (α : idAutSquareZero f hI x') :
    idAutSquareZeroTensor f hI x' α =
      (LinearEquiv.ofBijective (TensorProduct.lift (idAutSquareZeroTensorBilin f hI x'))
          sorry).symm α := sorry

/-- Underlying `F`-isomorphism of a fibre automorphism of `x'`, as an automorphism
of `ofObj p x'`. -/
def infAutToOfObjAut {x' : p.Fiber A'} (α : Aut x') :
    Aut (ofObj p (fiberInclusion.obj x')) :=
  Fiber.isoMk
    { hom := fiberInclusion.map α.hom
      inv := fiberInclusion.map α.inv
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- Inverse of `infAutToOfObjAut`, recovering a fibre automorphism of `x'`. -/
def infAutOfObjAutToInf {x' : p.Fiber A'}
    (β : Aut (ofObj p (fiberInclusion.obj x'))) : Aut x' :=
  Fiber.isoMk
    { hom := β.hom.1
      inv := β.inv.1
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- Group isomorphism `Aut x' ≃* Aut (ofObj p x')` on underlying total arrows. -/
def infAutMulEquivOfObj (x' : p.Fiber A') :
    Aut x' ≃* Aut (ofObj p (fiberInclusion.obj x')) where
  toFun := infAutToOfObjAut
  invFun := infAutOfObjAutToInf
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-- Selected identity-pushforward comparison `ofObj p x ≅ (𝟙)_* (ofObj p x)`. -/
def infAutIdPushforwardIso (x : F) :
    ofObj p x ≅ pushforwardObj p (𝟙 (p.obj x)) (ofObj p x) :=
  Fiber.isoMk
    { hom := pushforwardHom p (𝟙 (p.obj x)) (ofObj p x)
      inv :=
        @IsCocartesian.map _ _ _ _ p _ _ _ _ (𝟙 (p.obj x))
          (pushforwardHom p (𝟙 (p.obj x)) (ofObj p x)) inferInstance _
          (𝟙 x) (IsHomLift.id rfl)
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- Group isomorphism from `Aut x'` to automorphisms of the selected identity
pushforward, which is the value of `autFunctor` at `infAutIdUnder`. -/
def infAutMulEquivSelf (x' : p.Fiber A') :
    Aut x' ≃*
      Aut (pushforwardObj p (infAutIdUnder x').hom (ofObj p (fiberInclusion.obj x'))) :=
  (infAutMulEquivOfObj x').trans
    (Aut.autMulEquivOfIso (infAutIdPushforwardIso (fiberInclusion.obj x')))

/-- Identity fibre of `autFunctor` along `A' → A`. -/
abbrev infAutIdFiberBase (x' : p.Fiber A') :=
  autIdFiber (fiberInclusion.obj x') (infAutIdToBase f x')

/-- Transport of `Inf(x'/x)` into the identity fibre of `autFunctor` along `f`. -/
def infAutToIdFiber {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ] :
    infinitesimalAut p f φ ≃ infAutIdFiberBase f x' where
  toFun α := ⟨infAutMulEquivSelf x' α.val, sorry⟩
  invFun β := ⟨(infAutMulEquivSelf x').symm β.val, sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- `infAutToIdFiber` acts by `infAutMulEquivSelf` on underlying automorphisms. -/
theorem infAutToIdFiber_apply {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    (α : infinitesimalAut p f φ) :
    (infAutToIdFiber f φ α).val = infAutMulEquivSelf x' α.val := sorry

/-- (RS) comparison of `autFunctor` on the self-product square of `f`. -/
def infAutSelfPullbackComparison (hf : Function.Surjective f.hom) (x' : p.Fiber A') :
    (autFunctor p (fiberInclusion.obj x')).obj (infAutSelfPullbackUnder f x') ≃
      Types.PullbackObj
        ((autFunctor p (fiberInclusion.obj x')).map (infAutIdToBase f x'))
        ((autFunctor p (fiberInclusion.obj x')).map (infAutIdToBase f x')) :=
  Equiv.ofBijective
    (autFunctorComparison p (fiberInclusion.obj x')
      (infAutIdToBase f x') (infAutIdToBase f x')
      (infAutSelfPullbackFstUnder f x') (infAutSelfPullbackSndUnder f x')
      (isPullback_infAutSelfPullbackUnder f x'))
    (HasRimSchlessinger.autFunctorComparison_bijective p (fiberInclusion.obj x')
      (infAutIdToBase f x') (infAutIdToBase f x')
      (infAutSelfPullbackFstUnder f x') (infAutSelfPullbackSndUnder f x')
      (isPullback_infAutSelfPullbackUnder f x') (infAutIdToBase_surjective f hf x'))

/-- Pairing of identity fibres along `f` with the identity fibre along
`A' ×_A A' ⟶ A`. -/
def infAutSelfPullbackEquiv (hf : Function.Surjective f.hom) (x' : p.Fiber A') :
    infAutIdFiberBase f x' × infAutIdFiberBase f x' ≃
      autIdFiber (fiberInclusion.obj x') (infAutSelfPullbackToBase f x') where
  toFun αβ :=
    ⟨(infAutSelfPullbackComparison f hf x').symm ⟨⟨αβ.1.val, αβ.2.val⟩, sorry⟩, sorry⟩
  invFun γ :=
    ⟨⟨(infAutSelfPullbackComparison f hf x' γ.val).1.1, sorry⟩,
      ⟨(infAutSelfPullbackComparison f hf x' γ.val).1.2, sorry⟩⟩
  left_inv := sorry
  right_inv := sorry

/-- Transport of identity fibres along the Under-isomorphism `selfPullbackIso`. -/
def infAutSelfPullbackIsoFiberEquiv (x' : p.Fiber A') :
    autIdFiber (fiberInclusion.obj x') (infAutSelfPullbackToBase f x') ≃
      autIdFiber (fiberInclusion.obj x')
        (infAutSquareZeroPullbackFstUnder f hI x' ≫ infAutIdToBase f x') where
  toFun α :=
    ⟨pushforwardAut p (infAutSelfPullbackIsoUnder f hI x').hom
        (ofObj p (fiberInclusion.obj x')) α.val, sorry⟩
  invFun β :=
    ⟨pushforwardAut p (infAutSelfPullbackIsoUnder f hI x').inv
        (ofObj p (fiberInclusion.obj x')) β.val, sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- The object `k → k[I]` of `Under (p.obj x0)`. -/
def infAutResidueSquareZeroUnder (x0 : p.Fiber (residue Λ k)) :
    Under (p.obj (fiberInclusion.obj x0)) :=
  Under.mk (eqToHom x0.property ≫ residueToSquareZero (kerModule f hI))

/-- The identity object `k → k` of `Under (p.obj x0)`. -/
def infAutResidueIdUnder (x0 : p.Fiber (residue Λ k)) :
    Under (p.obj (fiberInclusion.obj x0)) :=
  Under.mk (eqToHom x0.property)

/-- The restriction `(k → k[I]) ⟶ (k → k)` in `Under (p.obj x0)`. -/
def infAutResidueSquareZeroToIdUnder (x0 : p.Fiber (residue Λ k)) :
    infAutResidueSquareZeroUnder f hI x0 ⟶ infAutResidueIdUnder x0 :=
  Under.homMk (squareZeroToResidue Λ k (kerModule f hI)) sorry

/-- Identity fibre of `autFunctor` at `x0` along `k → k[I] ⟶ k`, as `Lift(id_{x0}, k[I])`. -/
def idAutSquareZeroAtResidue (x0 : p.Fiber (residue Λ k)) :
    Subgroup
      (Aut (pushforwardObj p (infAutResidueSquareZeroUnder f hI x0).hom
        (ofObj p (fiberInclusion.obj x0)))) :=
  autIdFiber (fiberInclusion.obj x0) (infAutResidueSquareZeroToIdUnder f hI x0)

/-- Membership in `idAutSquareZeroAtResidue` is the identity-fibre condition along
`infAutResidueSquareZeroToIdUnder`. -/
theorem mem_idAutSquareZeroAtResidue (x0 : p.Fiber (residue Λ k))
    (α : Aut (pushforwardObj p (infAutResidueSquareZeroUnder f hI x0).hom
      (ofObj p (fiberInclusion.obj x0)))) :
    α ∈ idAutSquareZeroAtResidue f hI x0 ↔
      α ∈ autIdFiber (fiberInclusion.obj x0)
        (infAutResidueSquareZeroToIdUnder f hI x0) := sorry

/-- Selected `k[I]`-pushforward arrow of a residue-fibre object. -/
def infAutResidueSquareZeroHom (x0 : p.Fiber (residue Λ k)) :
    fiberInclusion.obj x0 ⟶
      fiberInclusion.obj
        (pushforwardObj p (infAutResidueSquareZeroUnder f hI x0).hom
          (ofObj p (fiberInclusion.obj x0))) :=
  pushforwardHom p (infAutResidueSquareZeroUnder f hI x0).hom
    (ofObj p (fiberInclusion.obj x0))

/-- The selected `k[I]`-pushforward of a residue object is strongly cocartesian over
`residueToSquareZero`. -/
instance instIsStronglyCocartesian_infAutResidueSquareZeroHom
    (x0 : p.Fiber (residue Λ k)) :
    p.IsStronglyCocartesian (residueToSquareZero (kerModule f hI))
      (infAutResidueSquareZeroHom f hI x0) := sorry

/-- Vertical `k[I]`-pushforward comparison induced by a residue-fibre isomorphism. -/
def infAutSquareZeroFiberIsoOfFiberIso {y0 z0 : p.Fiber (residue Λ k)}
    (α : y0 ≅ z0) :
    pushforwardObj p (infAutResidueSquareZeroUnder f hI y0).hom
        (ofObj p (fiberInclusion.obj y0)) ≅
      pushforwardObj p (infAutResidueSquareZeroUnder f hI z0).hom
        (ofObj p (fiberInclusion.obj z0)) :=
  isoMk
    { hom :=
        @IsCocartesian.map _ _ _ _ p _ _ _ _
          (residueToSquareZero (kerModule f hI))
          (infAutResidueSquareZeroHom f hI y0) inferInstance _
          (fiberInclusion.map α.hom ≫ infAutResidueSquareZeroHom f hI z0) sorry
      inv :=
        @IsCocartesian.map _ _ _ _ p _ _ _ _
          (residueToSquareZero (kerModule f hI))
          (infAutResidueSquareZeroHom f hI z0) inferInstance _
          (fiberInclusion.map α.inv ≫ infAutResidueSquareZeroHom f hI y0) sorry
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- Composite base arrow `A' → k → k[I]` through the selected residue of `x'`. -/
def infAutSquareZeroResidueCompBase (x' : p.Fiber A') :
    p.obj (fiberInclusion.obj x') ⟶ squareZero Λ k (kerModule f hI) :=
  toResidue (p.obj (fiberInclusion.obj x')) ≫
    eqToHom (residuePushforward p (fiberInclusion.obj x')).property.symm ≫
      (infAutResidueSquareZeroUnder f hI
        (residuePushforward p (fiberInclusion.obj x'))).hom

/-- Composite lift `x' ⟶ residue(x') ⟶ (k[I])_* residue(x')`. -/
def infAutSquareZeroResidueCompHom (x' : p.Fiber A') :
    fiberInclusion.obj x' ⟶
      fiberInclusion.obj
        (pushforwardObj p
          (infAutResidueSquareZeroUnder f hI
            (residuePushforward p (fiberInclusion.obj x'))).hom
          (ofObj p (residuePushforwardObj p (fiberInclusion.obj x')))) :=
  pushforwardHom p (toResidue (p.obj (fiberInclusion.obj x')))
      (ofObj p (fiberInclusion.obj x')) ≫
    infAutResidueSquareZeroHom f hI (residuePushforward p (fiberInclusion.obj x'))

/-- The two factorizations of `A' → k[I]` agree after composing with an identity. -/
theorem infAutSquareZeroObjIso_base_eq (x' : p.Fiber A') :
    infAutSquareZeroResidueCompBase f hI x' =
      (infAutSquareZeroUnder f hI x').hom ≫ 𝟙 (squareZero Λ k (kerModule f hI)) :=
  sorry

/-- The composite selected lift `x' ⟶ residue(x') ⟶ (k[I])_* residue(x')` lifts its
displayed base arrow. -/
theorem infAutSquareZeroResidueComp_isHomLift (x' : p.Fiber A') :
    p.IsHomLift (infAutSquareZeroResidueCompBase f hI x')
      (infAutSquareZeroResidueCompHom f hI x') := sorry

/-- The composite `x' ⟶ residue(x') ⟶ (k[I])_* residue(x')` is strongly cocartesian. -/
instance instIsStronglyCocartesian_infAutSquareZeroResidueComp (x' : p.Fiber A') :
    p.IsStronglyCocartesian (infAutSquareZeroResidueCompBase f hI x')
      (infAutSquareZeroResidueCompHom f hI x') := sorry

/-- The selected `k[I]`-pushforward arrow of `x'` lifts `A' → k[I]`. -/
theorem infAutSquareZeroObj_isHomLift (x' : p.Fiber A') :
    p.IsHomLift (infAutSquareZeroUnder f hI x').hom
      (pushforwardHom p (infAutSquareZeroUnder f hI x').hom
        (ofObj p (fiberInclusion.obj x'))) := sorry

/-- Forward comparison of `(A' → k[I])_* x'` with `(k → k[I])_* residue(x')`. -/
def infAutSquareZeroObjHom (x' : p.Fiber A') :
    (pushforwardObj p (infAutSquareZeroUnder f hI x').hom
        (ofObj p (fiberInclusion.obj x'))).1 ⟶
      (pushforwardObj p
          (infAutResidueSquareZeroUnder f hI
            (residuePushforward p (fiberInclusion.obj x'))).hom
          (ofObj p (residuePushforwardObj p (fiberInclusion.obj x')))).1 :=
  homLiftMap p
    (infAutSquareZeroUnder f hI x').hom
    (pushforwardHom p (infAutSquareZeroUnder f hI x').hom
      (ofObj p (fiberInclusion.obj x')))
    inferInstance
    (𝟙 (squareZero Λ k (kerModule f hI)))
    (infAutSquareZeroResidueCompBase f hI x')
    (infAutSquareZeroObjIso_base_eq f hI x')
    (infAutSquareZeroResidueCompHom f hI x')
    (infAutSquareZeroResidueComp_isHomLift f hI x')

/-- Reverse comparison of `(k → k[I])_* residue(x')` with `(A' → k[I])_* x'`. -/
def infAutSquareZeroObjInv (x' : p.Fiber A') :
    (pushforwardObj p
          (infAutResidueSquareZeroUnder f hI
            (residuePushforward p (fiberInclusion.obj x'))).hom
          (ofObj p (residuePushforwardObj p (fiberInclusion.obj x')))).1 ⟶
      (pushforwardObj p (infAutSquareZeroUnder f hI x').hom
        (ofObj p (fiberInclusion.obj x'))).1 :=
  homLiftMap p
    (infAutSquareZeroResidueCompBase f hI x')
    (infAutSquareZeroResidueCompHom f hI x')
    (instIsStronglyCocartesian_infAutSquareZeroResidueComp f hI x')
    (𝟙 (squareZero Λ k (kerModule f hI)))
    (infAutSquareZeroUnder f hI x').hom
    (infAutSquareZeroObjIso_base_eq f hI x').symm
    (pushforwardHom p (infAutSquareZeroUnder f hI x').hom
      (ofObj p (fiberInclusion.obj x')))
    (infAutSquareZeroObj_isHomLift f hI x')

/-- Fibre isomorphism `(A' → k[I])_* x' ≅ (k → k[I])_* residue(x')`. -/
def infAutSquareZeroObjIso (x' : p.Fiber A') :
    pushforwardObj p (infAutSquareZeroUnder f hI x').hom
        (ofObj p (fiberInclusion.obj x')) ≅
      pushforwardObj p
        (infAutResidueSquareZeroUnder f hI
          (residuePushforward p (fiberInclusion.obj x'))).hom
        (ofObj p (residuePushforwardObj p (fiberInclusion.obj x'))) :=
  isoMk
    { hom := infAutSquareZeroObjHom f hI x'
      inv := infAutSquareZeroObjInv f hI x'
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- The composite `x' ⟶ x ⟶ x0` lifts `toResidue` of the domain of `x'`. -/
theorem infAut_comp_isHomLift {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] :
    p.IsHomLift (toResidue (p.obj (fiberInclusion.obj x'))) (φ ≫ ψ) := sorry

/-- The composite `x' ⟶ x ⟶ x0` is cocartesian over `toResidue`. -/
theorem infAut_comp_isCocartesian {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    p.IsCocartesian (toResidue (p.obj (fiberInclusion.obj x'))) (φ ≫ ψ) := sorry

/-- Unique fibre isomorphism between the selected residue pushforward of `x'` and
the given residue pushforward `x0` of `x`. -/
def infAutResidueFiberIso {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    residuePushforward p (fiberInclusion.obj x') ≅ x0 :=
  Fiber.isoMk
    (@IsCocartesian.codomainUniqueUpToIso _ _ _ _ p _ _ _ _
      (toResidue (p.obj (fiberInclusion.obj x')))
      (pushforwardHom p (toResidue (p.obj (fiberInclusion.obj x')))
        (ofObj p (fiberInclusion.obj x')))
      inferInstance _ (φ ≫ ψ) (infAut_comp_isCocartesian f φ ψ))
    sorry

/-- Canonical fibre isomorphism `(A' → k[I])_* x' ≅ (k → k[I])_* x0`, via the selected
residue of `x'` and `infAutResidueFiberIso`. -/
def infAutResidueSquareZeroIso {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    pushforwardObj p (infAutSquareZeroUnder f hI x').hom
        (ofObj p (fiberInclusion.obj x')) ≅
      pushforwardObj p (infAutResidueSquareZeroUnder f hI x0).hom
        (ofObj p (fiberInclusion.obj x0)) :=
  (infAutSquareZeroObjIso f hI x').trans
    (infAutSquareZeroFiberIsoOfFiberIso f hI (infAutResidueFiberIso f φ ψ))

/-- Group isomorphism `Lift(id_{residue(x')}, k[I]) ≃* Lift(id_{x0}, k[I])` induced by
`infAutResidueSquareZeroIso`. -/
def infAutIdAutSquareZeroResidueMulEquiv {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    idAutSquareZero f hI x' ≃* idAutSquareZeroAtResidue f hI x0 where
  toFun α := ⟨Aut.autMulEquivOfIso (infAutResidueSquareZeroIso f hI φ ψ) α.val, sorry⟩
  invFun β :=
    ⟨(Aut.autMulEquivOfIso (infAutResidueSquareZeroIso f hI φ ψ)).symm β.val, sorry⟩
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-- Restriction of an identity-fibre automorphism along `A' ×_k k[I] ⟶ A` and
`A' ×_k k[I] ⟶ k[I]`, after composing with the residue pushforward `x ⟶ x0`. This
replays `liftsSquareZeroComparison` on identity fibres of `autFunctor`. -/
def infAutSquareZeroComparison {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    autIdFiber (fiberInclusion.obj x')
        (infAutSquareZeroPullbackFstUnder f hI x' ≫ infAutIdToBase f x') →
      infAutIdFiberBase f x' × idAutSquareZeroAtResidue f hI x0 :=
  fun γ ↦
    (⟨pushforwardAut p (infAutSquareZeroPullbackFstUnder f hI x')
        (ofObj p (fiberInclusion.obj x')) γ.val, sorry⟩,
      ⟨Aut.autMulEquivOfIso (infAutResidueSquareZeroIso f hI φ ψ)
        (pushforwardAut p (infAutSquareZeroPullbackSndUnder f hI x')
          (ofObj p (fiberInclusion.obj x')) γ.val), sorry⟩)

/-- The reconstructed Aut-fibre comparison of 90.17.5.3 is bijective. -/
theorem infAutSquareZeroComparison_bijective {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    Function.Bijective (infAutSquareZeroComparison f hI φ ψ) := sorry

/-- The bijection of 90.17.5.3 on Aut identity fibres, as an equivalence. -/
def infAutSquareZeroPullbackEquiv {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    autIdFiber (fiberInclusion.obj x')
        (infAutSquareZeroPullbackFstUnder f hI x' ≫ infAutIdToBase f x') ≃
      infAutIdFiberBase f x' × idAutSquareZeroAtResidue f hI x0 :=
  Equiv.ofBijective (infAutSquareZeroComparison f hI φ ψ)
    (infAutSquareZeroComparison_bijective f hI φ ψ)

/-- The underlying function of `infAutSquareZeroPullbackEquiv` is
`infAutSquareZeroComparison`. -/
theorem infAutSquareZeroPullbackEquiv_spec {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    (infAutSquareZeroPullbackEquiv f hI φ ψ).toFun =
      infAutSquareZeroComparison f hI φ ψ := sorry

/-- The first component of `infAutSquareZeroPullbackEquiv` is pushforward along the
first projection of `A' ×_k k[I]`. -/
theorem infAutSquareZeroPullbackEquiv_fst {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (γ : autIdFiber (fiberInclusion.obj x')
      (infAutSquareZeroPullbackFstUnder f hI x' ≫ infAutIdToBase f x')) :
    (infAutSquareZeroPullbackEquiv f hI φ ψ γ).1.val =
      pushforwardAut p (infAutSquareZeroPullbackFstUnder f hI x')
        (ofObj p (fiberInclusion.obj x')) γ.val := sorry

/-- The second component of `infAutSquareZeroPullbackEquiv` is pushforward along the
second projection of `A' ×_k k[I]`, transported to `Lift(id_{x0}, k[I])` by
`infAutResidueSquareZeroIso`. -/
theorem infAutSquareZeroPullbackEquiv_snd {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (γ : autIdFiber (fiberInclusion.obj x')
      (infAutSquareZeroPullbackFstUnder f hI x' ≫ infAutIdToBase f x')) :
    (infAutSquareZeroPullbackEquiv f hI φ ψ γ).2.val =
      Aut.autMulEquivOfIso (infAutResidueSquareZeroIso f hI φ ψ)
        (pushforwardAut p (infAutSquareZeroPullbackSndUnder f hI x')
          (ofObj p (fiberInclusion.obj x')) γ.val) := sorry

/-- The composite bijection Φ of the Aut-fibre analogues of 90.17.5.1–3, on
identity fibres of `autFunctor`. -/
def infAutPairFiberEquiv (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    infAutIdFiberBase f x' × infAutIdFiberBase f x' ≃
      infAutIdFiberBase f x' × idAutSquareZeroAtResidue f hI x0 :=
  (infAutSelfPullbackEquiv f hf x').trans
    ((infAutSelfPullbackIsoFiberEquiv f hI x').trans
      (infAutSquareZeroPullbackEquiv f hI φ ψ))

/-- The composite bijection Φ on `Inf(x'/x)`, as in Lemma 90.17.5. -/
def infAutPairEquiv (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    infinitesimalAut p f φ × infinitesimalAut p f φ ≃
      infinitesimalAut p f φ × idAutSquareZeroAtResidue f hI x0 :=
  ((infAutToIdFiber f φ).prodCongr (infAutToIdFiber f φ)).trans
    ((infAutPairFiberEquiv f hI hf φ ψ).trans
      ((infAutToIdFiber f φ).symm.prodCongr (Equiv.refl _)))

/-- Φ commutes with first projections. -/
theorem infAutPairEquiv_fst (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (α β : infinitesimalAut p f φ) :
    (infAutPairEquiv f hI hf φ ψ (α, β)).1 = α := sorry

/-- The inverse of Φ commutes with first projections. -/
theorem infAutPairEquiv_symm_fst (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (α : infinitesimalAut p f φ) (θ : idAutSquareZeroAtResidue f hI x0) :
    ((infAutPairEquiv f hI hf φ ψ).symm (α, θ)).1 = α := sorry

/-- The acting group `Inf_{x0}(F) ⊗[k] I`. -/
abbrev infAutTensor (x0 : p.Fiber (residue Λ k)) :=
  infinitesimalAutomorphismsAt p x0
      (pushforwardObj p (residueToDualNumber Λ k) x0) (infAutChosenHom p x0) ⊗[k]
    kerModule f hI

/-- `infAutTensor` is the tensor product of `Inf_{x0}(F)` with `kerModule f hI`. -/
theorem infAutTensor_def (x0 : p.Fiber (residue Λ k)) :
    infAutTensor f hI x0 =
      infinitesimalAutomorphismsAt p x0
          (pushforwardObj p (residueToDualNumber Λ k) x0) (infAutChosenHom p x0) ⊗[k]
        kerModule f hI := sorry

/-- Dual-number comparison of identity-tangent Aut-carriers induced by
`infAutResidueFiberIso`. -/
def infAutResidueDualNumberIso {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    idTangentSpaceObj p (residuePushforwardObj p (fiberInclusion.obj x')) ≅
      idTangentSpaceObj p (fiberInclusion.obj x0) :=
  fiberIso_of_fiberIso p (infAutResidueFiberIso f φ ψ)
    (infAutIdTangentHom p (residuePushforward p (fiberInclusion.obj x')))
    (infAutIdTangentHom p x0)

/-- Group isomorphism `T_id Aut(selected residue of x') ≃* T_id Aut(x0)`. -/
def infAutResidueIdTangentMulEquiv {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    idTangentSpace p (residuePushforwardObj p (fiberInclusion.obj x')) ≃*
      idTangentSpace p (fiberInclusion.obj x0) where
  toFun α := ⟨Aut.autMulEquivOfIso (infAutResidueDualNumberIso f φ ψ) α.val, sorry⟩
  invFun β := ⟨(Aut.autMulEquivOfIso (infAutResidueDualNumberIso f φ ψ)).symm β.val, sorry⟩
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-- Canonical `k`-linear isomorphism `T_id Aut(selected residue of x') ≃ T_id Aut(x0)`. -/
def infAutResidueIdTangentLinearEquiv {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    idTangentSpace p (residuePushforwardObj p (fiberInclusion.obj x')) ≃ₗ[k]
      idTangentSpace p (fiberInclusion.obj x0) where
  toFun := (infAutResidueIdTangentMulEquiv f φ ψ).toFun
  invFun := (infAutResidueIdTangentMulEquiv f φ ψ).invFun
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

/-- Composite identification `T_id Aut(x') ≃ₗ[k] Inf_{x0}(F)`. -/
def infAutIdTangentInfLinearEquiv {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    idTangentSpace p (fiberInclusion.obj x') ≃ₗ[k]
      infinitesimalAutomorphismsAt p x0
        (pushforwardObj p (residueToDualNumber Λ k) x0) (infAutChosenHom p x0) :=
  (idTangentSpaceLinearEquiv p (fiberInclusion.obj x')).trans
    ((infAutResidueIdTangentLinearEquiv f φ ψ).trans
      (infinitesimalAutomorphismsAtLinearEquiv p x0
        (pushforwardObj p (residueToDualNumber Λ k) x0) (infAutChosenHom p x0)).symm)

/-- Transport of `Inf_{x0}(F) ⊗[k] I` to `Lift(id_{x0}, k[I])`, via `idAutSquareZeroTensor`
and the residue comparison `infAutIdAutSquareZeroResidueMulEquiv`. -/
def infAutTensorToSquareZero {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    infAutTensor f hI x0 ≃ idAutSquareZeroAtResidue f hI x0 :=
  (TensorProduct.congr (infAutIdTangentInfLinearEquiv f φ ψ)
        (LinearEquiv.refl k (kerModule f hI))).symm.toEquiv.trans
    ((idAutSquareZeroTensor f hI x').symm.toEquiv.trans
      (infAutIdAutSquareZeroResidueMulEquiv f hI φ ψ).toEquiv)

/-- Construction-level action of `Lift(id_{x0}, k[I])` on `Inf(x'/x)`. -/
def infAutVAddSquareZero (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : idAutSquareZeroAtResidue f hI x0) (α : infinitesimalAut p f φ) :
    infinitesimalAut p f φ :=
  ((infAutPairEquiv f hI hf φ ψ).symm (α, θ)).2

/-- Construction-level difference of two infinitesimal automorphisms, as an
element of `Lift(id_{x0}, k[I])`. -/
def infAutVSubSquareZero (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (α' α : infinitesimalAut p f φ) : idAutSquareZeroAtResidue f hI x0 :=
  (infAutPairEquiv f hI hf φ ψ (α, α')).2

/-- Action of `Inf_{x0}(F) ⊗[k] I` on `Inf(x'/x)`, transported from
`infAutVAddSquareZero`. -/
def infAutVAdd (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : infAutTensor f hI x0) (α : infinitesimalAut p f φ) :
    infinitesimalAut p f φ :=
  infAutVAddSquareZero f hI hf φ ψ (infAutTensorToSquareZero f hI φ ψ θ) α

/-- Difference of two infinitesimal automorphisms, as an element of
`Inf_{x0}(F) ⊗[k] I`. -/
def infAutVSub (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (α' α : infinitesimalAut p f φ) : infAutTensor f hI x0 :=
  (infAutTensorToSquareZero f hI φ ψ).symm (infAutVSubSquareZero f hI hf φ ψ α' α)

/-- Tensor-space addition is construction-level addition after applying
`infAutTensorToSquareZero`. -/
theorem infAutVAdd_spec (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : infAutTensor f hI x0) (α : infinitesimalAut p f φ) :
    infAutVAdd f hI hf φ ψ θ α =
      infAutVAddSquareZero f hI hf φ ψ (infAutTensorToSquareZero f hI φ ψ θ) α :=
  sorry

/-- Tensor-space subtraction is construction-level subtraction, transported by
`infAutTensorToSquareZero`. -/
theorem infAutVSub_spec (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (α' α : infinitesimalAut p f φ) :
    infAutVSub f hI hf φ ψ α' α =
      (infAutTensorToSquareZero f hI φ ψ).symm
        (infAutVSubSquareZero f hI hf φ ψ α' α) := sorry

/-- The additive action of `Inf_{x0}(F) ⊗[k] I` on `Inf(x'/x)`. -/
@[reducible]
def instAddAction_infAut (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    AddAction (infAutTensor f hI x0) (infinitesimalAut p f φ) where
  vadd := infAutVAdd f hI hf φ ψ
  add_vadd := sorry
  zero_vadd := sorry

/-- `instAddAction_infAut` acts by `infAutVAdd`. -/
theorem instAddAction_infAut_vadd (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : infAutTensor f hI x0) (α : infinitesimalAut p f φ) :
    (instAddAction_infAut f hI hf φ ψ).vadd θ α = infAutVAdd f hI hf φ ψ θ α :=
  sorry

/-- `Inf(x'/x)` is a torsor under `Inf_{x0}(F) ⊗[k] I`. No extra nonempty hypothesis
is required, because `Inf(x'/x)` is a group. -/
@[reducible]
def instAddTorsor_infAut (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    AddTorsor (infAutTensor f hI x0) (infinitesimalAut p f φ) :=
  { instAddAction_infAut f hI hf φ ψ with
    vsub := infAutVSub f hI hf φ ψ
    vsub_vadd' := sorry
    vadd_vsub' := sorry }

/-- `instAddTorsor_infAut` subtracts by `infAutVSub`. -/
theorem instAddTorsor_infAut_vsub (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (α' α : infinitesimalAut p f φ) :
    (instAddTorsor_infAut f hI hf φ ψ).vsub α' α = infAutVSub f hI hf φ ψ α' α :=
  sorry

end CategoryTheory.Functor
