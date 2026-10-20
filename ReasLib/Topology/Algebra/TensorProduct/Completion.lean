/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import ReasLib.Topology.Algebra.TensorProduct.LinearTopology

/-!
# Completed tensor product of linearly topologized modules

The completed tensor product of linearly topologized modules `M` and `N` is the inverse limit
of the stage tensors `(M ⧸ U) ⊗[R] (N ⧸ V)` as `U` and `V` run through open submodules. This is
the completion of `TensorProduct.Linear R M N`, equally the inverse limit of the quotients
`(M ⊗[R] N) ⧸ (U ⊗ N + M ⊗ V)`.
-/

@[expose] public section

noncomputable section

open TensorProduct

universe u

namespace TensorProduct

variable (R M N : Type u)
variable [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
variable [AddCommGroup N] [Module R N] [TopologicalSpace N]

/-- The completed tensor product, realized as the inverse limit of the stage tensors
`(M ⧸ U) ⊗[R] (N ⧸ V)` over open submodules `U ⊆ M` and `V ⊆ N`. -/
def Completed : Type u :=
  { f : ∀ (U : {U : Submodule R M // IsOpen (U : Set M)})
      (V : {V : Submodule R N // IsOpen (V : Set N)}),
      (M ⧸ U.1) ⊗[R] (N ⧸ V.1) //
    ∀ (U U' : {U : Submodule R M // IsOpen (U : Set M)})
      (V V' : {V : Submodule R N // IsOpen (V : Set N)})
      (hUU' : U.1 ≤ U'.1) (hVV' : V.1 ≤ V'.1),
      map (Submodule.factor hUU') (Submodule.factor hVV') (f U V) = f U' V' }

/-- The inverse limit of the quotients `(M ⊗[R] N) ⧸ (U ⊗ N + M ⊗ V)` as open submodules
`U ⊆ M` and `V ⊆ N` run through a fundamental system. -/
def QuotientLimit : Type u :=
  { f : ∀ (U : {U : Submodule R M // IsOpen (U : Set M)})
      (V : {V : Submodule R N // IsOpen (V : Set N)}),
      (M ⊗[R] N) ⧸ fundamentalSubmodule R M N U.1 V.1 //
    ∀ (U U' : {U : Submodule R M // IsOpen (U : Set M)})
      (V V' : {V : Submodule R N // IsOpen (V : Set N)})
      (hUU' : U.1 ≤ U'.1) (hVV' : V.1 ≤ V'.1),
      Submodule.mapQ (fundamentalSubmodule R M N U.1 V.1)
          (fundamentalSubmodule R M N U'.1 V'.1) LinearMap.id
          (fundamentalSubmodule_mono R M N hUU' hVV') (f U V) =
        f U' V' }

namespace QuotientLimit

/-- Zero in the inverse limit of quotients by fundamental submodules. -/
instance instZero : Zero (QuotientLimit R M N) where
  zero := ⟨0, sorry⟩

/-- Pointwise addition of compatible families of quotients by fundamental submodules. -/
instance instAdd : Add (QuotientLimit R M N) where
  add x y := ⟨x.1 + y.1, sorry⟩

/-- Pointwise negation of compatible families of quotients by fundamental submodules. -/
instance instNeg : Neg (QuotientLimit R M N) where
  neg x := ⟨-x.1, sorry⟩

/-- Pointwise subtraction of compatible families of quotients by fundamental submodules. -/
instance instSub : Sub (QuotientLimit R M N) where
  sub x y := ⟨x.1 - y.1, sorry⟩

/-- Natural-number scalar multiplication on compatible families of quotients. -/
instance instNSmul : SMul ℕ (QuotientLimit R M N) where
  smul n x := ⟨n • x.1, sorry⟩

/-- Integer scalar multiplication on compatible families of quotients. -/
instance instZSmul : SMul ℤ (QuotientLimit R M N) where
  smul n x := ⟨n • x.1, sorry⟩

/-- Scalar multiplication by `R` on compatible families of quotients. -/
instance instSMul : SMul R (QuotientLimit R M N) where
  smul r x := ⟨r • x.1, sorry⟩

/-- The inverse limit of quotients by fundamental submodules is an abelian group. -/
instance instAddCommGroup : AddCommGroup (QuotientLimit R M N) :=
  Subtype.val_injective.addCommGroup (fun x : QuotientLimit R M N ↦ x.1)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The inverse limit of quotients by fundamental submodules is an `R`-module. -/
instance instModule : Module R (QuotientLimit R M N) :=
  Subtype.val_injective.module R
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    (fun _ _ ↦ rfl)

/-- Projection from the inverse limit onto `(M ⊗[R] N) ⧸ (U ⊗ N + M ⊗ V)`. -/
def π (U : Submodule R M) (V : Submodule R N)
    (hU : IsOpen (U : Set M)) (hV : IsOpen (V : Set N)) :
    QuotientLimit R M N →ₗ[R] (M ⊗[R] N) ⧸ fundamentalSubmodule R M N U V where
  toFun f := f.1 ⟨U, hU⟩ ⟨V, hV⟩
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

/-- Compatibility of a family in the inverse limit of quotients by fundamental submodules. -/
theorem compatible (f : QuotientLimit R M N) (U U' : Submodule R M) (V V' : Submodule R N)
    (hU : IsOpen (U : Set M)) (hU' : IsOpen (U' : Set M))
    (hV : IsOpen (V : Set N)) (hV' : IsOpen (V' : Set N))
    (hUU' : U ≤ U') (hVV' : V ≤ V') :
    Submodule.mapQ (fundamentalSubmodule R M N U V) (fundamentalSubmodule R M N U' V')
        LinearMap.id (fundamentalSubmodule_mono R M N hUU' hVV')
        (π R M N U V hU hV f) =
      π R M N U' V' hU' hV' f := sorry

end QuotientLimit

namespace Completed

/-- Zero in the completed tensor product is the zero family of stage tensors. -/
instance instZero : Zero (Completed R M N) where
  zero := ⟨0, sorry⟩

/-- Pointwise addition of compatible families of stage tensors. -/
instance instAdd : Add (Completed R M N) where
  add x y := ⟨x.1 + y.1, sorry⟩

/-- Pointwise negation of compatible families of stage tensors. -/
instance instNeg : Neg (Completed R M N) where
  neg x := ⟨-x.1, sorry⟩

/-- Pointwise subtraction of compatible families of stage tensors. -/
instance instSub : Sub (Completed R M N) where
  sub x y := ⟨x.1 - y.1, sorry⟩

/-- Natural-number scalar multiplication on compatible families of stage tensors. -/
instance instNSmul : SMul ℕ (Completed R M N) where
  smul n x := ⟨n • x.1, sorry⟩

/-- Integer scalar multiplication on compatible families of stage tensors. -/
instance instZSmul : SMul ℤ (Completed R M N) where
  smul n x := ⟨n • x.1, sorry⟩

/-- Scalar multiplication by `R` on compatible families of stage tensors. -/
instance instSMul : SMul R (Completed R M N) where
  smul r x := ⟨r • x.1, sorry⟩

/-- The completed tensor product is an abelian group under pointwise operations. -/
instance instAddCommGroup : AddCommGroup (Completed R M N) :=
  Subtype.val_injective.addCommGroup (fun x : Completed R M N ↦ x.1)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The completed tensor product is an `R`-module under pointwise operations. -/
instance instModule : Module R (Completed R M N) :=
  Subtype.val_injective.module R
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    (fun _ _ ↦ rfl)

/-- The inverse-limit topology on the completed tensor product, induced from the product of
discrete topologies on the stage tensors. -/
instance instTopologicalSpace : TopologicalSpace (Completed R M N) :=
  TopologicalSpace.induced Subtype.val <|
    ⨅ (U : {U : Submodule R M // IsOpen (U : Set M)})
      (V : {V : Submodule R N // IsOpen (V : Set N)}),
      TopologicalSpace.induced (fun f ↦ f U V)
        (⊥ : TopologicalSpace ((M ⧸ U.1) ⊗[R] (N ⧸ V.1)))

variable [IsTopologicalAddGroup M] [IsTopologicalAddGroup N]
variable [IsLinearTopology R M] [IsLinearTopology R N]

/-- Addition and negation are continuous on the completed tensor product. -/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (Completed R M N) := sorry

/-- The completed tensor product is linearly topologized. -/
instance instIsLinearTopology : IsLinearTopology R (Completed R M N) := sorry

/-- The completed tensor product is separated. -/
instance instT0Space : T0Space (Completed R M N) := sorry

/-- The completed tensor product carries its canonical additive uniformity. -/
instance instUniformSpace : UniformSpace (Completed R M N) :=
  IsTopologicalAddGroup.rightUniformSpace (Completed R M N)

set_option backward.privateInPublic true in
/-- The component formula for `Completed.of` is compatible with quotient transitions. -/
private theorem of_compatible (x : Linear R M N) {U U' : Submodule R M} {V V' : Submodule R N}
    (hUU' : U ≤ U') (hVV' : V ≤ V') :
    map (Submodule.factor hUU') (Submodule.factor hVV')
        (map U.mkQ V.mkQ (Linear.equiv R M N x)) =
      map U'.mkQ V'.mkQ (Linear.equiv R M N x) := sorry

set_option backward.privateInPublic true in
/-- The component formula for `Completed.of` preserves addition. -/
private theorem of_map_add (x y : Linear R M N) (U : Submodule R M) (V : Submodule R N) :
    map U.mkQ V.mkQ (Linear.equiv R M N (x + y)) =
      map U.mkQ V.mkQ (Linear.equiv R M N x) +
        map U.mkQ V.mkQ (Linear.equiv R M N y) := sorry

set_option backward.privateInPublic true in
/-- The component formula for `Completed.of` preserves scalar multiplication. -/
private theorem of_map_smul (r : R) (x : Linear R M N) (U : Submodule R M) (V : Submodule R N) :
    map U.mkQ V.mkQ (Linear.equiv R M N (r • x)) =
      r • map U.mkQ V.mkQ (Linear.equiv R M N x) := sorry

set_option backward.privateInPublic true in
/-- Canonical map from the linearly topologized tensor product to its inverse-limit completion. -/
def of : Linear R M N →ₗ[R] Completed R M N where
  toFun x := ⟨fun U V ↦ map U.1.mkQ V.1.mkQ (Linear.equiv R M N x),
    fun U U' V V' hUU' hVV' ↦ of_compatible R M N x hUU' hVV'⟩
  map_add' := fun x y =>
    Subtype.ext (funext fun U => funext fun V => of_map_add R M N x y U.1 V.1)
  map_smul' := fun r x =>
    Subtype.ext (funext fun U => funext fun V => of_map_smul R M N r x U.1 V.1)

/-- Projection from the completed tensor product onto the stage `(M ⧸ U) ⊗[R] (N ⧸ V)`. -/
def π (U : Submodule R M) (V : Submodule R N)
    (hU : IsOpen (U : Set M)) (hV : IsOpen (V : Set N)) :
    Completed R M N →ₗ[R] (M ⧸ U) ⊗[R] (N ⧸ V) where
  toFun f := f.1 ⟨U, hU⟩ ⟨V, hV⟩
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

/-- Stage equivalences intertwine `Submodule.factor` on quotient modules with the
`Submodule.mapQ` identity transition of quotients by fundamental submodules. -/
theorem stageEquiv_naturality {U U' : Submodule R M} {V V' : Submodule R N}
    (hUU' : U ≤ U') (hVV' : V ≤ V') (x : (M ⧸ U) ⊗[R] (N ⧸ V)) :
    quotientTensorQuotientEquiv U' V' (map (Submodule.factor hUU') (Submodule.factor hVV') x) =
      Submodule.mapQ (fundamentalSubmodule R M N U V) (fundamentalSubmodule R M N U' V')
        LinearMap.id (fundamentalSubmodule_mono R M N hUU' hVV')
        (quotientTensorQuotientEquiv U V x) := sorry

set_option backward.privateInPublic true in
/-- The forward component family in the quotient-limit equivalence is compatible. -/
private theorem equivQuotientLimit_forward_compatible (f : Completed R M N)
    {U U' : Submodule R M} {V V' : Submodule R N}
    (hU : IsOpen (U : Set M)) (hU' : IsOpen (U' : Set M))
    (hV : IsOpen (V : Set N)) (hV' : IsOpen (V' : Set N))
    (hUU' : U ≤ U') (hVV' : V ≤ V') :
    Submodule.mapQ (fundamentalSubmodule R M N U V) (fundamentalSubmodule R M N U' V')
        LinearMap.id (fundamentalSubmodule_mono R M N hUU' hVV')
        (quotientTensorQuotientEquiv U V (f.1 ⟨U, hU⟩ ⟨V, hV⟩)) =
      quotientTensorQuotientEquiv U' V' (f.1 ⟨U', hU'⟩ ⟨V', hV'⟩) := sorry

set_option backward.privateInPublic true in
/-- The backward component family in the quotient-limit equivalence is compatible. -/
private theorem equivQuotientLimit_backward_compatible (g : QuotientLimit R M N)
    {U U' : Submodule R M} {V V' : Submodule R N}
    (hU : IsOpen (U : Set M)) (hU' : IsOpen (U' : Set M))
    (hV : IsOpen (V : Set N)) (hV' : IsOpen (V' : Set N))
    (hUU' : U ≤ U') (hVV' : V ≤ V') :
    map (Submodule.factor hUU') (Submodule.factor hVV')
        ((quotientTensorQuotientEquiv U V).symm (g.1 ⟨U, hU⟩ ⟨V, hV⟩)) =
      (quotientTensorQuotientEquiv U' V').symm (g.1 ⟨U', hU'⟩ ⟨V', hV'⟩) := sorry

set_option backward.privateInPublic true in
/-- The prescribed component formulas for the quotient-limit equivalence compose to the identity. -/
private theorem equivQuotientLimit_left_inv (f : Completed R M N) (U : Submodule R M)
    (V : Submodule R N) (hU : IsOpen (U : Set M)) (hV : IsOpen (V : Set N)) :
    (quotientTensorQuotientEquiv U V).symm
        (quotientTensorQuotientEquiv U V (f.1 ⟨U, hU⟩ ⟨V, hV⟩)) = f.1 ⟨U, hU⟩ ⟨V, hV⟩ := sorry

set_option backward.privateInPublic true in
/-- The prescribed component formulas for the quotient-limit equivalence compose to the identity. -/
private theorem equivQuotientLimit_right_inv (g : QuotientLimit R M N) (U : Submodule R M)
    (V : Submodule R N) (hU : IsOpen (U : Set M)) (hV : IsOpen (V : Set N)) :
    quotientTensorQuotientEquiv U V
        ((quotientTensorQuotientEquiv U V).symm (g.1 ⟨U, hU⟩ ⟨V, hV⟩)) = g.1 ⟨U, hU⟩ ⟨V, hV⟩ := sorry

set_option backward.privateInPublic true in
/-- The forward component family in the quotient-limit equivalence preserves addition. -/
private theorem equivQuotientLimit_map_add (f g : Completed R M N) (U : Submodule R M)
    (V : Submodule R N) (hU : IsOpen (U : Set M)) (hV : IsOpen (V : Set N)) :
    quotientTensorQuotientEquiv U V ((f.1 ⟨U, hU⟩ ⟨V, hV⟩) + (g.1 ⟨U, hU⟩ ⟨V, hV⟩)) =
      quotientTensorQuotientEquiv U V (f.1 ⟨U, hU⟩ ⟨V, hV⟩) +
        quotientTensorQuotientEquiv U V (g.1 ⟨U, hU⟩ ⟨V, hV⟩) := sorry

set_option backward.privateInPublic true in
/-- The forward component family in the quotient-limit equivalence preserves scalar multiplication. -/
private theorem equivQuotientLimit_map_smul (r : R) (f : Completed R M N) (U : Submodule R M)
    (V : Submodule R N) (hU : IsOpen (U : Set M)) (hV : IsOpen (V : Set N)) :
    quotientTensorQuotientEquiv U V (r • f.1 ⟨U, hU⟩ ⟨V, hV⟩) =
      r • quotientTensorQuotientEquiv U V (f.1 ⟨U, hU⟩ ⟨V, hV⟩) := sorry

set_option backward.privateInPublic true in
/-- The canonical linear equivalence between the two inverse-limit presentations
`lim (M ⧸ U) ⊗[R] (N ⧸ V)` and `lim (M ⊗[R] N) ⧸ (U ⊗ N + M ⊗ V)`. -/
def equivQuotientLimit : Completed R M N ≃ₗ[R] QuotientLimit R M N where
  toFun f := ⟨fun U V ↦ quotientTensorQuotientEquiv U.1 V.1 (f.1 U V),
    fun U U' V V' hUU' hVV' ↦
      equivQuotientLimit_forward_compatible R M N f U.2 U'.2 V.2 V'.2 hUU' hVV'⟩
  invFun g := ⟨fun U V ↦ (quotientTensorQuotientEquiv U.1 V.1).symm (g.1 U V),
    fun U U' V V' hUU' hVV' ↦
      equivQuotientLimit_backward_compatible R M N g U.2 U'.2 V.2 V'.2 hUU' hVV'⟩
  left_inv := fun f =>
    Subtype.ext (funext fun U => funext fun V =>
      equivQuotientLimit_left_inv R M N f U.1 V.1 U.2 V.2)
  right_inv := fun g =>
    Subtype.ext (funext fun U => funext fun V =>
      equivQuotientLimit_right_inv R M N g U.1 V.1 U.2 V.2)
  map_add' := fun f g =>
    Subtype.ext (funext fun U => funext fun V =>
      equivQuotientLimit_map_add R M N f g U.1 V.1 U.2 V.2)
  map_smul' := fun r f =>
    Subtype.ext (funext fun U => funext fun V =>
      equivQuotientLimit_map_smul R M N r f U.1 V.1 U.2 V.2)

/-- Componentwise, the inverse-limit identification is the stage equivalence. -/
theorem equivQuotientLimit_π (U : Submodule R M) (V : Submodule R N)
    (hU : IsOpen (U : Set M)) (hV : IsOpen (V : Set N)) (f : Completed R M N) :
    QuotientLimit.π R M N U V hU hV (equivQuotientLimit R M N f) =
      quotientTensorQuotientEquiv U V (π R M N U V hU hV f) := sorry

/-- The canonical map to the completion, evaluated at a stage, is the stage quotient map. -/
theorem π_of (U : Submodule R M) (V : Submodule R N)
    (hU : IsOpen (U : Set M)) (hV : IsOpen (V : Set N)) (x : Linear R M N) :
    π R M N U V hU hV (of R M N x) = map U.mkQ V.mkQ (Linear.equiv R M N x) := sorry

/-- Compatibility of a completed tensor with the inverse system of stage tensors. -/
theorem compatible (f : Completed R M N) (U U' : Submodule R M) (V V' : Submodule R N)
    (hU : IsOpen (U : Set M)) (hU' : IsOpen (U' : Set M))
    (hV : IsOpen (V : Set N)) (hV' : IsOpen (V' : Set N))
    (hUU' : U ≤ U') (hVV' : V ≤ V') :
    map (Submodule.factor hUU') (Submodule.factor hVV')
      (π R M N U V hU hV f) = π R M N U' V' hU' hV' f := sorry

/-- The canonical map from the linearly topologized tensor product has dense range. -/
theorem denseRange_of : DenseRange (of R M N : Linear R M N → Completed R M N) := sorry

/-- The inverse-limit completed tensor product is complete for its additive uniformity. -/
instance instCompleteSpace : CompleteSpace (Completed R M N) := sorry

/-- The canonical map into the completed tensor product is uniform-inducing. -/
theorem isUniformInducing_of :
    IsUniformInducing (of R M N : Linear R M N → Completed R M N) := sorry

variable [TopologicalSpace R] [ContinuousSMul R M] [ContinuousSMul R N]

/-- Scalar multiplication on the completed tensor product is continuous under continuous factor actions. -/
instance instContinuousSMul : ContinuousSMul R (Completed R M N) := sorry

/-- Linear continuous maps out of the completed tensor product are determined by composition
with `Completed.of`. -/
theorem ext_of {P : Type u} [AddCommGroup P] [Module R P] [TopologicalSpace P] [T2Space P]
    {f g : Completed R M N →ₗ[R] P} (hf : Continuous f) (hg : Continuous g)
    (h : f.comp (of R M N) = g.comp (of R M N)) : f = g := sorry

end Completed

end TensorProduct
