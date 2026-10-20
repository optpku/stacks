module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.TangentComparison
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Module
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SelfPullbackComparison

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
private theorem isPullback_infAutSelfPullbackUnder (x' : p.Fiber A') :
    IsPullback (infAutSelfPullbackFstUnder f x') (infAutSelfPullbackSndUnder f x')
      (infAutIdToBase f x') (infAutIdToBase f x') := sorry

/-- The underlying algebra map of `infAutIdToBase` is surjective. -/
private theorem infAutIdToBase_surjective (hf : Function.Surjective f.hom) (x' : p.Fiber A') :
    Function.Surjective (infAutIdToBase f x').right.hom := sorry

/-- Identity fibre of `autFunctor p x` along an under-morphism. -/
def autIdFiber (x : F) {U V : Under (p.obj x)} (φ : U ⟶ V) :
    Subgroup (Aut (pushforwardObj p U.hom (ofObj p x))) := by
  let S : Set (Aut (pushforwardObj p U.hom (ofObj p x))) :=
    {α | pushforwardAut p φ (ofObj p x) α = 1}
  have laws : (∀ {α β}, α ∈ S → β ∈ S → α * β ∈ S) ∧
      (1 ∈ S) ∧ (∀ {α}, α ∈ S → α⁻¹ ∈ S) := sorry
  exact {
    carrier := S, mul_mem' := laws.1, one_mem' := laws.2.1,
    inv_mem' := laws.2.2 }

/-- Membership in `autIdFiber` is the identity-fibre condition for `pushforwardAut`. -/
theorem mem_autIdFiber (x : F) {U V : Under (p.obj x)} (φ : U ⟶ V)
    (α : Aut (pushforwardObj p U.hom (ofObj p x))) :
    α ∈ autIdFiber x φ ↔
      pushforwardAut p φ (ofObj p x) α =
        (1 : Aut (pushforwardObj p V.hom (ofObj p x))) := Iff.rfl

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
  Iff.rfl

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
    AddCommGroup (idAutSquareZero f hI x') := by
  have laws :
      (∀ a b c : idAutSquareZero f hI x', (a + b) + c = a + (b + c)) ∧
      (∀ a : idAutSquareZero f hI x', 0 + a = a) ∧
      (∀ a : idAutSquareZero f hI x', a + 0 = a) ∧
      (∀ a : idAutSquareZero f hI x', -a + a = 0) ∧
      (∀ a b : idAutSquareZero f hI x', a + b = b + a) := sorry
  exact {
    add_assoc := laws.1, zero_add := laws.2.1, add_zero := laws.2.2.1,
    nsmul := nsmulRec, neg_add_cancel := laws.2.2.2.1, zsmul := zsmulRec,
    add_comm := laws.2.2.2.2 }

/-- The `k`-module structure on the identity fibre of `autFunctor` at `k[I]`. -/
instance instModule_idAutSquareZero (x' : p.Fiber A') :
    Module k (idAutSquareZero f hI x') := by
  have laws :
      (∀ a : idAutSquareZero f hI x', (1 : k) • a = a) ∧
      (∀ (r s : k) (a : idAutSquareZero f hI x'), (r * s) • a = r • (s • a)) ∧
      (∀ r : k, r • (0 : idAutSquareZero f hI x') = 0) ∧
      (∀ (r : k) (a b : idAutSquareZero f hI x'), r • (a + b) = r • a + r • b) ∧
      (∀ (r s : k) (a : idAutSquareZero f hI x'), (r + s) • a = r • a + s • a) ∧
      (∀ a : idAutSquareZero f hI x', (0 : k) • a = 0) := sorry
  exact {
    one_smul := laws.1, mul_smul := laws.2.1, smul_zero := laws.2.2.1,
    smul_add := laws.2.2.2.1, add_smul := laws.2.2.2.2.1, zero_smul := laws.2.2.2.2.2 }

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
      kerModule f hI →ₗ[k] idAutSquareZero f hI x' := by
  let raw (α : idTangentSpace p (fiberInclusion.obj x')) (v : kerModule f hI) :=
    pushforwardAut p (infAutSpanUnder f hI x' v)
      (ofObj p (fiberInclusion.obj x')) α.val
  let Mem : Prop := ∀ α v, raw α v ∈ idAutSquareZero f hI x'
  let b (h : Mem) (α : idTangentSpace p (fiberInclusion.obj x')) (v : kerModule f hI) :
      idAutSquareZero f hI x' := ⟨raw α v, h α v⟩
  have laws : Mem ∧ ∀ h : Mem,
      (∀ α β v, b h (α + β) v = b h α v + b h β v) ∧
      (∀ (r : k) α v, b h (r • α) v = r • b h α v) ∧
      (∀ α v w, b h α (v + w) = b h α v + b h α w) ∧
      (∀ (r : k) α v, b h α (r • v) = r • b h α v) := sorry
  exact LinearMap.mk₂ k (b laws.1) (laws.2 laws.1).1 (laws.2 laws.1).2.1
    (laws.2 laws.1).2.2.1 (laws.2 laws.1).2.2.2

/-- On pure tensors, `idAutSquareZeroTensorBilin` applies `pushforwardAut` of
`infAutSpanUnder v`. -/
theorem idAutSquareZeroTensorBilin_apply (x' : p.Fiber A')
    (α : idTangentSpace p (fiberInclusion.obj x')) (v : kerModule f hI) :
    (idAutSquareZeroTensorBilin f hI x' α v).val =
      pushforwardAut p (infAutSpanUnder f hI x' v)
        (ofObj p (fiberInclusion.obj x')) α.val := rfl

/-- Canonical `k`-linear identification of `Lift(id, k[I])` with
`T_id Aut(x') ⊗[k] I`. -/
def idAutSquareZeroTensor (x' : p.Fiber A') :
    idAutSquareZero f hI x' ≃ₗ[k]
      idTangentSpace p (fiberInclusion.obj x') ⊗[k] kerModule f hI :=
  (LinearEquiv.ofBijective (TensorProduct.lift (idAutSquareZeroTensorBilin f hI x')) sorry).symm

/-- The inverse tensor comparison is the lift of the span-singleton bilinear map. -/
theorem idAutSquareZeroTensor_spec (x' : p.Fiber A')
    (θ : idTangentSpace p (fiberInclusion.obj x') ⊗[k] kerModule f hI) :
    (idAutSquareZeroTensor f hI x').symm θ =
      TensorProduct.lift (idAutSquareZeroTensorBilin f hI x') θ := rfl

/-- Underlying `F`-isomorphism of a fibre automorphism of `x'`, as an automorphism
of `ofObj p x'`. -/
def infAutToOfObjAut {x' : p.Fiber A'} (α : Aut x') :
    Aut (ofObj p (fiberInclusion.obj x')) := by
  let h := fiberInclusion.map α.hom
  let i := fiberInclusion.map α.inv
  have laws : (h ≫ i = 𝟙 _) ∧ (i ≫ h = 𝟙 _) ∧
      p.IsHomLift (𝟙 (p.obj (fiberInclusion.obj x'))) h := sorry
  exact Fiber.isoMk {
    hom := h, inv := i, hom_inv_id := laws.1,
    inv_hom_id := laws.2.1 } laws.2.2

/-- Inverse of `infAutToOfObjAut`, recovering a fibre automorphism of `x'`. -/
def infAutOfObjAutToInf {x' : p.Fiber A'}
    (β : Aut (ofObj p (fiberInclusion.obj x'))) : Aut x' := by
  let h := β.hom.1
  let i := β.inv.1
  have laws : (h ≫ i = 𝟙 _) ∧ (i ≫ h = 𝟙 _) ∧
      p.IsHomLift (𝟙 A') h := sorry
  exact Fiber.isoMk {
    hom := h, inv := i, hom_inv_id := laws.1,
    inv_hom_id := laws.2.1 } laws.2.2

/-- Group isomorphism `Aut x' ≃* Aut (ofObj p x')` on underlying total arrows. -/
def infAutMulEquivOfObj (x' : p.Fiber A') :
    Aut x' ≃* Aut (ofObj p (fiberInclusion.obj x')) := by
  have laws :
      Function.LeftInverse (infAutOfObjAutToInf (p := p)) (infAutToOfObjAut (x' := x')) ∧
      Function.RightInverse (infAutOfObjAutToInf (p := p)) (infAutToOfObjAut (x' := x')) ∧
      (∀ α β : Aut x', infAutToOfObjAut (α * β) = infAutToOfObjAut α * infAutToOfObjAut β) := sorry
  exact {
    toFun := infAutToOfObjAut, invFun := infAutOfObjAutToInf,
    left_inv := laws.1, right_inv := laws.2.1, map_mul' := laws.2.2 }

/-- Selected identity-pushforward comparison `ofObj p x ≅ (𝟙)_* (ofObj p x)`. -/
def infAutIdPushforwardIso (x : F) :
    ofObj p x ≅ pushforwardObj p (𝟙 (p.obj x)) (ofObj p x) := by
  let h := pushforwardHom p (𝟙 (p.obj x)) (ofObj p x)
  let i := @IsCocartesian.map _ _ _ _ p _ _ _ _ (𝟙 (p.obj x)) h inferInstance _
    (𝟙 x) (IsHomLift.id rfl)
  have laws : (h ≫ i = 𝟙 _) ∧ (i ≫ h = 𝟙 _) ∧
      p.IsHomLift (𝟙 (p.obj x)) h := sorry
  exact Fiber.isoMk {
    hom := h, inv := i, hom_inv_id := laws.1,
    inv_hom_id := laws.2.1 } laws.2.2

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
    infinitesimalAut p f φ ≃ infAutIdFiberBase f x' := by
  let e := infAutMulEquivSelf x'
  let Mem : Prop :=
    (∀ α : infinitesimalAut p f φ, e α.val ∈ infAutIdFiberBase f x') ∧
    (∀ β : infAutIdFiberBase f x', e.symm β.val ∈ infinitesimalAut p f φ)
  let forward (h : Mem) (α : infinitesimalAut p f φ) : infAutIdFiberBase f x' :=
    ⟨e α.val, h.1 α⟩
  let backward (h : Mem) (β : infAutIdFiberBase f x') : infinitesimalAut p f φ :=
    ⟨e.symm β.val, h.2 β⟩
  have laws : Mem ∧ ∀ h : Mem,
      Function.LeftInverse (backward h) (forward h) ∧
      Function.RightInverse (backward h) (forward h) := sorry
  exact {
    toFun := forward laws.1, invFun := backward laws.1,
    left_inv := (laws.2 laws.1).1, right_inv := (laws.2 laws.1).2 }

/-- `infAutToIdFiber` acts by `infAutMulEquivSelf` on underlying automorphisms. -/
theorem infAutToIdFiber_apply {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    (α : infinitesimalAut p f φ) :
    (infAutToIdFiber f φ α).val = infAutMulEquivSelf x' α.val := rfl

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
      (by exact isPullback_infAutSelfPullbackUnder f x'))
    (HasRimSchlessinger.autFunctorComparison_bijective p (fiberInclusion.obj x')
      (infAutIdToBase f x') (infAutIdToBase f x')
      (infAutSelfPullbackFstUnder f x') (infAutSelfPullbackSndUnder f x')
      (by exact isPullback_infAutSelfPullbackUnder f x') (by exact infAutIdToBase_surjective f hf x'))

/-- Pairing of identity fibres along `f` with the identity fibre along
`A' ×_A A' ⟶ A`. -/
def infAutSelfPullbackEquiv (hf : Function.Surjective f.hom) (x' : p.Fiber A') :
    infAutIdFiberBase f x' × infAutIdFiberBase f x' ≃
      autIdFiber (fiberInclusion.obj x') (infAutSelfPullbackToBase f x') := by
  let e := infAutSelfPullbackComparison f hf x'
  let Compatible : Prop := ∀ αβ : infAutIdFiberBase f x' × infAutIdFiberBase f x',
    (autFunctor p (fiberInclusion.obj x')).map (infAutIdToBase f x') αβ.1.val =
      (autFunctor p (fiberInclusion.obj x')).map (infAutIdToBase f x') αβ.2.val
  let raw (h : Compatible) (αβ : infAutIdFiberBase f x' × infAutIdFiberBase f x') :=
    e.symm ⟨⟨αβ.1.val, αβ.2.val⟩, h αβ⟩
  let Mem (h : Compatible) : Prop :=
    (∀ αβ, raw h αβ ∈ autIdFiber (fiberInclusion.obj x') (infAutSelfPullbackToBase f x')) ∧
    (∀ γ : autIdFiber (fiberInclusion.obj x') (infAutSelfPullbackToBase f x'),
      (e γ.val).1.1 ∈ infAutIdFiberBase f x' ∧ (e γ.val).1.2 ∈ infAutIdFiberBase f x')
  let forward (h : Compatible) (m : Mem h)
      (αβ : infAutIdFiberBase f x' × infAutIdFiberBase f x') :
      autIdFiber (fiberInclusion.obj x') (infAutSelfPullbackToBase f x') :=
    ⟨raw h αβ, m.1 αβ⟩
  let backward (h : Compatible) (m : Mem h)
      (γ : autIdFiber (fiberInclusion.obj x') (infAutSelfPullbackToBase f x')) :
      infAutIdFiberBase f x' × infAutIdFiberBase f x' :=
    (⟨(e γ.val).1.1, (m.2 γ).1⟩, ⟨(e γ.val).1.2, (m.2 γ).2⟩)
  have laws : Compatible ∧ ∀ h : Compatible, Mem h ∧ ∀ m : Mem h,
      Function.LeftInverse (backward h m) (forward h m) ∧
      Function.RightInverse (backward h m) (forward h m) := sorry
  exact {
    toFun := forward laws.1 (laws.2 laws.1).1,
    invFun := backward laws.1 (laws.2 laws.1).1,
    left_inv := ((laws.2 laws.1).2 (laws.2 laws.1).1).1,
    right_inv := ((laws.2 laws.1).2 (laws.2 laws.1).1).2 }

/-- Transport of identity fibres along the Under-isomorphism `selfPullbackIso`. -/
def infAutSelfPullbackIsoFiberEquiv (x' : p.Fiber A') :
    autIdFiber (fiberInclusion.obj x') (infAutSelfPullbackToBase f x') ≃
      autIdFiber (fiberInclusion.obj x')
        (infAutSquareZeroPullbackFstUnder f hI x' ≫ infAutIdToBase f x') := by
  let forwardRaw := pushforwardAut p (infAutSelfPullbackIsoUnder f hI x').hom
    (ofObj p (fiberInclusion.obj x'))
  let backwardRaw := pushforwardAut p (infAutSelfPullbackIsoUnder f hI x').inv
    (ofObj p (fiberInclusion.obj x'))
  let S := autIdFiber (fiberInclusion.obj x') (infAutSelfPullbackToBase f x')
  let T := autIdFiber (fiberInclusion.obj x')
    (infAutSquareZeroPullbackFstUnder f hI x' ≫ infAutIdToBase f x')
  let Mem : Prop := (∀ α : S, forwardRaw α.val ∈ T) ∧
    (∀ β : T, backwardRaw β.val ∈ S)
  let forward (h : Mem) (α : S) : T := ⟨forwardRaw α.val, h.1 α⟩
  let backward (h : Mem) (β : T) : S := ⟨backwardRaw β.val, h.2 β⟩
  have laws : Mem ∧ ∀ h : Mem,
      Function.LeftInverse (backward h) (forward h) ∧
      Function.RightInverse (backward h) (forward h) := sorry
  exact {
    toFun := forward laws.1, invFun := backward laws.1,
    left_inv := (laws.2 laws.1).1, right_inv := (laws.2 laws.1).2 }

/-- The composite `x' ⟶ x ⟶ x0` lifts `toResidue` of the domain of `x'`. -/
private theorem infAut_comp_isHomLift {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] :
    p.IsHomLift (toResidue (p.obj (fiberInclusion.obj x'))) (φ ≫ ψ) := sorry

/-- The composite of a base lift with a residue pushforward is strongly cocartesian over the residue map. -/
private theorem infAut_comp_isStronglyCocartesian {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    p.IsStronglyCocartesian (toResidue (p.obj (fiberInclusion.obj x'))) (φ ≫ ψ) := sorry

/-- Restriction to the two projections gives a pair consisting of a base identity-fibre automorphism and a square-zero identity-fibre automorphism. -/
def infAutSquareZeroComparison (x' : p.Fiber A') :
    autIdFiber (fiberInclusion.obj x')
        (infAutSquareZeroPullbackFstUnder f hI x' ≫ infAutIdToBase f x') →
      infAutIdFiberBase f x' × idAutSquareZero f hI x' := by
  have laws : ∀ γ : autIdFiber (fiberInclusion.obj x')
      (infAutSquareZeroPullbackFstUnder f hI x' ≫ infAutIdToBase f x'),
      (pushforwardAut p (infAutSquareZeroPullbackFstUnder f hI x')
        (ofObj p (fiberInclusion.obj x')) γ.val ∈ infAutIdFiberBase f x') ∧
      (pushforwardAut p (infAutSquareZeroPullbackSndUnder f hI x')
        (ofObj p (fiberInclusion.obj x')) γ.val ∈ idAutSquareZero f hI x') := sorry
  exact fun γ ↦
    (⟨pushforwardAut p (infAutSquareZeroPullbackFstUnder f hI x')
      (ofObj p (fiberInclusion.obj x')) γ.val, (laws γ).1⟩,
    ⟨pushforwardAut p (infAutSquareZeroPullbackSndUnder f hI x')
      (ofObj p (fiberInclusion.obj x')) γ.val, (laws γ).2⟩)

/-- Restriction to the two projections is bijective on the identity fibres. -/
theorem infAutSquareZeroComparison_bijective (x' : p.Fiber A') :
    Function.Bijective (infAutSquareZeroComparison f hI x') := sorry

/-- The square-zero pullback identifies its base identity fibre with the product of the two identity fibres. -/
def infAutSquareZeroPullbackEquiv (x' : p.Fiber A') :
    autIdFiber (fiberInclusion.obj x')
        (infAutSquareZeroPullbackFstUnder f hI x' ≫ infAutIdToBase f x') ≃
      infAutIdFiberBase f x' × idAutSquareZero f hI x' :=
  Equiv.ofBijective (infAutSquareZeroComparison f hI x')
    (infAutSquareZeroComparison_bijective f hI x')

/-- The underlying function of `infAutSquareZeroPullbackEquiv` is
`infAutSquareZeroComparison`. -/
theorem infAutSquareZeroPullbackEquiv_spec (x' : p.Fiber A') :
    (infAutSquareZeroPullbackEquiv f hI x').toFun =
      infAutSquareZeroComparison f hI x' := rfl

/-- The first component of `infAutSquareZeroPullbackEquiv` is pushforward along the
first projection of `A' ×_k k[I]`. -/
theorem infAutSquareZeroPullbackEquiv_fst (x' : p.Fiber A')

    (γ : autIdFiber (fiberInclusion.obj x')
      (infAutSquareZeroPullbackFstUnder f hI x' ≫ infAutIdToBase f x')) :
    (infAutSquareZeroPullbackEquiv f hI x' γ).1.val =
      pushforwardAut p (infAutSquareZeroPullbackFstUnder f hI x')
        (ofObj p (fiberInclusion.obj x')) γ.val := rfl

/-- The second coordinate is restriction along the second square-zero pullback projection. -/
theorem infAutSquareZeroPullbackEquiv_snd (x' : p.Fiber A')

    (γ : autIdFiber (fiberInclusion.obj x')
      (infAutSquareZeroPullbackFstUnder f hI x' ≫ infAutIdToBase f x')) :
    (infAutSquareZeroPullbackEquiv f hI x' γ).2.val =
      pushforwardAut p (infAutSquareZeroPullbackSndUnder f hI x')
          (ofObj p (fiberInclusion.obj x')) γ.val := rfl

/-- The self-pullback and square-zero comparisons identify pairs of base identity-fibre automorphisms with an automorphism and its difference. -/
def infAutPairFiberEquiv (hf : Function.Surjective f.hom) (x' : p.Fiber A') :
    infAutIdFiberBase f x' × infAutIdFiberBase f x' ≃
      infAutIdFiberBase f x' × idAutSquareZero f hI x' :=
  (infAutSelfPullbackEquiv f hf x').trans
    ((infAutSelfPullbackIsoFiberEquiv f hI x').trans
      (infAutSquareZeroPullbackEquiv f hI x'))

/-- Pairs of relative infinitesimal automorphisms are identified with an automorphism and a square-zero difference. -/
def infAutPairEquiv (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ] :
    infinitesimalAut p f φ × infinitesimalAut p f φ ≃
      infinitesimalAut p f φ × idAutSquareZero f hI x' :=
  ((infAutToIdFiber f φ).prodCongr (infAutToIdFiber f φ)).trans
    ((infAutPairFiberEquiv f hI hf x').trans
      ((infAutToIdFiber f φ).symm.prodCongr (Equiv.refl _)))

/-- Φ commutes with first projections. -/
theorem infAutPairEquiv_fst (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    (α β : infinitesimalAut p f φ) :
    (infAutPairEquiv f hI hf φ (α, β)).1 = α := sorry

/-- The inverse of Φ commutes with first projections. -/
theorem infAutPairEquiv_symm_fst (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    (α : infinitesimalAut p f φ) (θ : idAutSquareZero f hI x') :
    ((infAutPairEquiv f hI hf φ).symm (α, θ)).1 = α := sorry

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
        kerModule f hI := rfl

/-- Composite identification `T_id Aut(x') ≃ₗ[k] Inf_{x0}(F)`. -/
def infAutIdTangentInfLinearEquiv {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    idTangentSpace p (fiberInclusion.obj x') ≃ₗ[k]
      infinitesimalAutomorphismsAt p x0
        (pushforwardObj p (residueToDualNumber Λ k) x0) (infAutChosenHom p x0) :=
  (@idTangentSpaceLinearEquivOfPushforward _ _ _ _ _ _ _ _ _ p inferInstance
    (fiberInclusion.obj x') x0 (φ ≫ ψ)
    (by exact infAut_comp_isStronglyCocartesian f φ ψ)).trans
      (infinitesimalAutomorphismsAtLinearEquiv p x0
        (pushforwardObj p (residueToDualNumber Λ k) x0) (infAutChosenHom p x0)).symm

/-- The infinitesimal-automorphism tensor space identifies with the square-zero identity fibre. -/
def infAutTensorToSquareZero {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    infAutTensor f hI x0 ≃ idAutSquareZero f hI x' :=
  (TensorProduct.congr (infAutIdTangentInfLinearEquiv f φ ψ)
        (LinearEquiv.refl k (kerModule f hI))).symm.toEquiv.trans
    (idAutSquareZeroTensor f hI x').symm.toEquiv

/-- A square-zero identity-fibre automorphism acts through the inverse pair comparison. -/
def infAutVAddSquareZero (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    (θ : idAutSquareZero f hI x') (α : infinitesimalAut p f φ) :
    infinitesimalAut p f φ :=
  ((infAutPairEquiv f hI hf φ).symm (α, θ)).2

/-- The second coordinate of the pair comparison is the square-zero difference. -/
def infAutVSubSquareZero (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    (α' α : infinitesimalAut p f φ) : idAutSquareZero f hI x' :=
  (infAutPairEquiv f hI hf φ (α, α')).2

/-- Action of `Inf_{x0}(F) ⊗[k] I` on `Inf(x'/x)`, transported from
`infAutVAddSquareZero`. -/
def infAutVAdd (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : infAutTensor f hI x0) (α : infinitesimalAut p f φ) :
    infinitesimalAut p f φ :=
  infAutVAddSquareZero f hI hf φ (infAutTensorToSquareZero f hI φ ψ θ) α

/-- Difference of two infinitesimal automorphisms, as an element of
`Inf_{x0}(F) ⊗[k] I`. -/
def infAutVSub (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (α' α : infinitesimalAut p f φ) : infAutTensor f hI x0 :=
  (infAutTensorToSquareZero f hI φ ψ).symm (infAutVSubSquareZero f hI hf φ α' α)

/-- Tensor-space addition is construction-level addition after applying
`infAutTensorToSquareZero`. -/
theorem infAutVAdd_spec (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : infAutTensor f hI x0) (α : infinitesimalAut p f φ) :
    infAutVAdd f hI hf φ ψ θ α =
      infAutVAddSquareZero f hI hf φ (infAutTensorToSquareZero f hI φ ψ θ) α :=
  rfl

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
        (infAutVSubSquareZero f hI hf φ α' α) := rfl

/-- The additive action of `Inf_{x0}(F) ⊗[k] I` on `Inf(x'/x)`. -/
@[reducible]
def infAutAddAction (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    AddAction (infAutTensor f hI x0) (infinitesimalAut p f φ) := by
  let act := infAutVAdd f hI hf φ ψ
  have laws : (∀ (a b : infAutTensor f hI x0) (α : infinitesimalAut p f φ),
      act (a + b) α = act a (act b α)) ∧
      (∀ α : infinitesimalAut p f φ, act 0 α = α) := sorry
  exact {
    vadd := act, add_vadd := laws.1, zero_vadd := laws.2 }

/-- `infAutAddAction` acts by `infAutVAdd`. -/
theorem infAutAddAction_vadd (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : infAutTensor f hI x0) (α : infinitesimalAut p f φ) :
    (infAutAddAction f hI hf φ ψ).vadd θ α = infAutVAdd f hI hf φ ψ θ α :=
  rfl

/-- `Inf(x'/x)` is a torsor under `Inf_{x0}(F) ⊗[k] I`. No extra nonempty hypothesis
is required, because `Inf(x'/x)` is a group. -/
@[reducible]
def infAutAddTorsor (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    AddTorsor (infAutTensor f hI x0) (infinitesimalAut p f φ) := by
  let act := infAutVAdd f hI hf φ ψ
  let diff := infAutVSub f hI hf φ ψ
  have laws : (∀ α β : infinitesimalAut p f φ, act (diff α β) β = α) ∧
      (∀ (θ : infAutTensor f hI x0) (α : infinitesimalAut p f φ), diff (act θ α) α = θ) := sorry
  exact {
    infAutAddAction f hI hf φ ψ with
    vsub := diff, nonempty := ⟨1⟩,
    vsub_vadd' := laws.1, vadd_vsub' := laws.2 }

/-- `infAutAddTorsor` subtracts by `infAutVSub`. -/
theorem infAutAddTorsor_vsub (hf : Function.Surjective f.hom) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (α' α : infinitesimalAut p f φ) :
    (infAutAddTorsor f hf hI φ ψ).vsub α' α = infAutVSub f hI hf φ ψ α' α :=
  rfl

/-- The tensor action of `θ` sends `α` to `α'` if and only if the transported
difference recovers `θ`. -/
theorem infAutAddTorsor_spec (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : infAutTensor f hI x0)
    (α α' : infinitesimalAut p f φ) :
    infAutVAdd f hI hf φ ψ θ α = α' ↔ infAutVSub f hI hf φ ψ α' α = θ := sorry

/-- The identity-tangent tensor space identifies linearly with the infinitesimal-automorphism tensor space. -/
def infAutTensorLinearEquiv (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    idTangentSpace p (fiberInclusion.obj x') ⊗[k] kerModule f hI ≃ₗ[k]
      infAutTensor f hI x0 :=
  TensorProduct.congr (infAutIdTangentInfLinearEquiv f φ ψ)
    (LinearEquiv.refl k (kerModule f hI))

/-- `infAutTensorLinearEquiv` is `TensorProduct.congr` of
`infAutIdTangentInfLinearEquiv` with the identity on `kerModule`. -/
theorem infAutTensorLinearEquiv_apply (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : idTangentSpace p (fiberInclusion.obj x') ⊗[k] kerModule f hI) :
    infAutTensorLinearEquiv f hI φ ψ θ =
      TensorProduct.congr (infAutIdTangentInfLinearEquiv f φ ψ)
        (LinearEquiv.refl k (kerModule f hI)) θ := rfl

end CategoryTheory.Functor
