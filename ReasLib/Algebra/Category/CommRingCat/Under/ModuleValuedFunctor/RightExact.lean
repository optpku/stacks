/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Tangent
public import ReasLib.Algebra.Category.ModuleCat.EilenbergWatts
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

universe u

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}

/-- The fixed-base tangent functor bundled together with a proof of right exactness. -/
noncomputable def rightExactTangent (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (hB : rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) :
    ModuleCat.{u} B.right ⥤ᵣ ModuleCat.{u} B.right :=
  ⟨F.tangent.fixedBase B, hB⟩

/-- The underlying functor of `rightExactTangent` is the fixed-base tangent functor. -/
theorem rightExactTangent_obj (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (hB : rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) :
    (F.rightExactTangent B hB).obj = F.tangent.fixedBase B := sorry

/-- The additive functor obtained from a right-exact fixed-base tangent functor. -/
private noncomputable def additiveTangent (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (hB : rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) :
    AdditiveFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right) :=
  (AdditiveFunctor.ofRightExact (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)).obj
    (F.rightExactTangent B hB)

/-- The underlying functor of `additiveTangent` is the fixed-base tangent functor. -/
private theorem additiveTangent_obj (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (hB : rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) :
    (F.additiveTangent B hB).obj = F.tangent.fixedBase B := sorry

/-- An additive tangent functor preserves binary biproducts. -/
private noncomputable def additiveTangentPreservesBinaryBiproducts
    (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (hB : rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) :
    PreservesBinaryBiproducts (F.additiveTangent B hB).obj :=
  preservesBinaryBiproducts_of_preservesBiproducts (F.additiveTangent B hB).obj

/-- A pointwise right-exact tangent functor carries a binary direct sum to the
canonical binary direct sum of its tangent values. -/
@[expose] noncomputable def tangentBiprodIso (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N₁ N₂ : ModuleCat.{u} B.right) :
    F.tangentObj B (N₁ ⊞ N₂) ≅ F.tangentObj B N₁ ⊞ F.tangentObj B N₂ where
  hom := biprod.lift ((F.tangent.fixedBase B).map biprod.fst)
    ((F.tangent.fixedBase B).map biprod.snd)
  inv := biprod.desc ((F.tangent.fixedBase B).map biprod.inl)
    ((F.tangent.fixedBase B).map biprod.inr)
  hom_inv_id := by
    letI : (F.tangent.fixedBase B).Additive :=
      rightExactFunctor_le_additiveFunctor _ _ _ (hF B)
    change biprod.lift ((F.tangent.fixedBase B).map (biprod.fst : N₁ ⊞ N₂ ⟶ N₁))
        ((F.tangent.fixedBase B).map biprod.snd) ≫
      biprod.desc ((F.tangent.fixedBase B).map biprod.inl)
        ((F.tangent.fixedBase B).map biprod.inr) =
      𝟙 ((F.tangent.fixedBase B).obj (N₁ ⊞ N₂))
    rw [biprod.lift_desc, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_add, biprod.total]
    exact (F.tangent.fixedBase B).map_id _
  inv_hom_id := by
    letI : (F.tangent.fixedBase B).Additive :=
      rightExactFunctor_le_additiveFunctor _ _ _ (hF B)
    change biprod.desc ((F.tangent.fixedBase B).map (biprod.inl : N₁ ⟶ N₁ ⊞ N₂))
        ((F.tangent.fixedBase B).map biprod.inr) ≫
      biprod.lift ((F.tangent.fixedBase B).map biprod.fst)
        ((F.tangent.fixedBase B).map biprod.snd) =
      𝟙 ((F.tangent.fixedBase B).obj N₁ ⊞ (F.tangent.fixedBase B).obj N₂)
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      simp [Category.assoc, ← Functor.map_comp]

/-- The first projection of `tangentBiprodIso` is induced by the first biproduct projection. -/
theorem tangentBiprodIso_hom_fst (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N₁ N₂ : ModuleCat.{u} B.right) :
    (F.tangentBiprodIso hF B N₁ N₂).hom ≫ biprod.fst =
      (F.tangent.fixedBase B).map biprod.fst := sorry

/-- The second projection of `tangentBiprodIso` is induced by the second biproduct projection. -/
theorem tangentBiprodIso_hom_snd (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N₁ N₂ : ModuleCat.{u} B.right) :
    (F.tangentBiprodIso hF B N₁ N₂).hom ≫ biprod.snd =
      (F.tangent.fixedBase B).map biprod.snd := sorry

/-- A distinct carrier for the argument-induced scalar action on a tangent module. -/
private def TangentArgumentCarrier (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right) : Type u :=
  F.tangentObj B N

/-- The argument-action carrier inherits the additive group of the tangent module. -/
private noncomputable def tangentArgumentCarrierAddCommGroup
    (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right) :
    AddCommGroup (TangentArgumentCarrier F hF B N) :=
  inferInstanceAs (AddCommGroup (F.tangentObj B N))

/-- Scalar multiplication on the argument-action carrier is induced by the tangent functor. -/
private noncomputable def tangentArgumentCarrierSMul
    (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right) :
    SMul B.right (TangentArgumentCarrier F hF B N) where
  smul b x := (F.tangent.fixedBase B).map (b • 𝟙 N) x

/-- The argument-induced scalar action distributes over tangent-vector addition. -/
private theorem tangentArgument_smul_add (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right)
    (b : B.right) (x y : TangentArgumentCarrier F hF B N) :
    -- Local instance justification (proof-local temporary data): the law uses the explicit named additive-group datum on the argument-action carrier.
    letI := tangentArgumentCarrierAddCommGroup F hF B N
    -- Local instance justification (proof-local temporary data): the law uses the explicit named scalar action on the argument-action carrier.
    letI := tangentArgumentCarrierSMul F hF B N
    b • (x + y) = b • x + b • y := sorry

/-- The argument-induced action is additive in the scalar. -/
private theorem tangentArgument_add_smul (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right)
    (b c : B.right) (x : TangentArgumentCarrier F hF B N) :
    -- Local instance justification (proof-local temporary data): the law uses the explicit named additive-group datum on the argument-action carrier.
    letI := tangentArgumentCarrierAddCommGroup F hF B N
    -- Local instance justification (proof-local temporary data): the law uses the explicit named scalar action on the argument-action carrier.
    letI := tangentArgumentCarrierSMul F hF B N
    (b + c) • x = b • x + c • x := sorry

/-- The argument-induced action is associative. -/
private theorem tangentArgument_mul_smul (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right)
    (b c : B.right) (x : TangentArgumentCarrier F hF B N) :
    -- Local instance justification (proof-local temporary data): the associativity law uses the explicit named scalar action on the argument-action carrier.
    letI := tangentArgumentCarrierSMul F hF B N
    (b * c) • x = b • c • x := sorry

/-- One acts trivially for the argument-induced scalar action. -/
private theorem tangentArgument_one_smul (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right)
    (x : TangentArgumentCarrier F hF B N) :
    -- Local instance justification (proof-local temporary data): the unit law uses the explicit named scalar action on the argument-action carrier.
    letI := tangentArgumentCarrierSMul F hF B N
    (1 : B.right) • x = x := sorry

/-- The module structure defined by functorial scalar multiplication in the argument. -/
private noncomputable def tangentArgumentCarrierModule
    (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right) :
    -- Local instance justification (proof-local temporary data): the `Module` result type requires the explicit named additive-group datum on the argument-action carrier.
    letI := tangentArgumentCarrierAddCommGroup F hF B N
    -- Local instance justification (proof-local temporary data): the `Module` result type requires the explicit named scalar action on the argument-action carrier.
    letI := tangentArgumentCarrierSMul F hF B N
    Module B.right (TangentArgumentCarrier F hF B N) :=
  -- Local instance justification (proof-local temporary data): `Module.ofMinimalAxioms` requires the explicit named additive-group datum on the argument-action carrier.
  letI := tangentArgumentCarrierAddCommGroup F hF B N
  -- Local instance justification (proof-local temporary data): `Module.ofMinimalAxioms` requires the explicit named scalar action on the argument-action carrier.
  letI := tangentArgumentCarrierSMul F hF B N
  Module.ofMinimalAxioms (tangentArgument_smul_add F hF B N)
    (tangentArgument_add_smul F hF B N) (tangentArgument_mul_smul F hF B N)
    (tangentArgument_one_smul F hF B N)

/-- Fixed-base tangent maps are linear for the argument-induced scalar actions. -/
private theorem tangentArgumentMap_smul (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) {N N' : ModuleCat.{u} B.right}
    (f : N ⟶ N') (b : B.right) (x : TangentArgumentCarrier F hF B N) :
    (F.tangent.fixedBase B).map f
        (@SMul.smul B.right (TangentArgumentCarrier F hF B N)
          (tangentArgumentCarrierSMul F hF B N) b x) =
      @SMul.smul B.right (TangentArgumentCarrier F hF B N')
        (tangentArgumentCarrierSMul F hF B N') ((RingHom.id B.right) b)
        ((F.tangent.fixedBase B).map f x) := sorry

/-- A fixed-base tangent map bundled for the argument-induced scalar actions. -/
private noncomputable def tangentArgumentMap (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) {N N' : ModuleCat.{u} B.right}
    (f : N ⟶ N') :
    -- Local instance justification (proof-local temporary data): source `ModuleCat.of` requires the explicit named additive-group datum on the argument-action carrier.
    letI := tangentArgumentCarrierAddCommGroup F hF B N
    -- Local instance justification (proof-local temporary data): source `ModuleCat.of` requires the explicit named scalar-action datum on the argument-action carrier.
    letI := tangentArgumentCarrierSMul F hF B N
    -- Local instance justification (proof-local temporary data): source `ModuleCat.of` requires the explicit named module datum on the argument-action carrier.
    letI := tangentArgumentCarrierModule F hF B N
    -- Local instance justification (proof-local temporary data): target `ModuleCat.of` requires the explicit named additive-group datum on the argument-action carrier.
    letI := tangentArgumentCarrierAddCommGroup F hF B N'
    -- Local instance justification (proof-local temporary data): target `ModuleCat.of` requires the explicit named scalar-action datum on the argument-action carrier.
    letI := tangentArgumentCarrierSMul F hF B N'
    -- Local instance justification (proof-local temporary data): target `ModuleCat.of` requires the explicit named module datum on the argument-action carrier.
    letI := tangentArgumentCarrierModule F hF B N'
    ModuleCat.of B.right (TangentArgumentCarrier F hF B N) ⟶
      ModuleCat.of B.right (TangentArgumentCarrier F hF B N') :=
  -- Local instance justification (proof-local temporary data): `ModuleCat.ofHom` requires the explicit source additive-group datum on the argument-action carrier.
  letI := tangentArgumentCarrierAddCommGroup F hF B N
  -- Local instance justification (proof-local temporary data): `ModuleCat.ofHom` requires the explicit source scalar-action datum on the argument-action carrier.
  letI := tangentArgumentCarrierSMul F hF B N
  -- Local instance justification (proof-local temporary data): `ModuleCat.ofHom` requires the explicit source module datum on the argument-action carrier.
  letI := tangentArgumentCarrierModule F hF B N
  -- Local instance justification (proof-local temporary data): `ModuleCat.ofHom` requires the explicit target additive-group datum on the argument-action carrier.
  letI := tangentArgumentCarrierAddCommGroup F hF B N'
  -- Local instance justification (proof-local temporary data): `ModuleCat.ofHom` requires the explicit target scalar-action datum on the argument-action carrier.
  letI := tangentArgumentCarrierSMul F hF B N'
  -- Local instance justification (proof-local temporary data): `ModuleCat.ofHom` requires the explicit target module datum on the argument-action carrier.
  letI := tangentArgumentCarrierModule F hF B N'
  ModuleCat.ofHom {
    toFun := fun x ↦ (F.tangent.fixedBase B).map f x
    map_add' := (F.tangent.fixedBase B).map f |>.hom.map_add
    map_smul' := tangentArgumentMap_smul F hF B f }

/-- Argument-action tangent maps preserve identity morphisms. -/
private theorem tangentArgumentMap_id (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right) :
    tangentArgumentMap F hF B (𝟙 N) = 𝟙 _ := sorry

/-- Argument-action tangent maps preserve composition. -/
private theorem tangentArgumentMap_comp (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) {N₁ N₂ N₃ : ModuleCat.{u} B.right}
    (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃) :
    tangentArgumentMap F hF B (f ≫ g) =
      tangentArgumentMap F hF B f ≫ tangentArgumentMap F hF B g := sorry

/-- The second functorial `B`-module structure on `TF(B, N)` has scalar action
`b • x = TF(B, b • 𝟙 N)(x)`. -/
noncomputable def tangentArgument (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) :
    ModuleCat.{u} B.right ⥤ ModuleCat.{u} B.right where
  obj N :=
    -- Local instance justification (proof-local temporary data): the object field's `ModuleCat.of` requires the explicit named additive-group datum on the argument-action carrier.
    letI := tangentArgumentCarrierAddCommGroup F hF B N
    -- Local instance justification (proof-local temporary data): the object field's `ModuleCat.of` requires the explicit named scalar-action datum on the argument-action carrier.
    letI := tangentArgumentCarrierSMul F hF B N
    -- Local instance justification (proof-local temporary data): the object field's `ModuleCat.of` requires the explicit named assembled module datum on the argument-action carrier.
    letI := tangentArgumentCarrierModule F hF B N
    ModuleCat.of B.right (TangentArgumentCarrier F hF B N)
  map f := tangentArgumentMap F hF B f
  map_id N := tangentArgumentMap_id F hF B N
  map_comp f g := tangentArgumentMap_comp F hF B f g

/-- The argument-action tangent functor is additive. -/
instance tangentArgument_additive (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) :
    (F.tangentArgument hF B).Additive where
  map_add {N N' f g} := by
    letI : (F.tangent.fixedBase B).Additive :=
      rightExactFunctor_le_additiveFunctor _ _ _ (hF B)
    ext element
    change ((F.tangent.fixedBase B).map (f + g)).hom element =
      ((F.tangent.fixedBase B).map f).hom element +
        ((F.tangent.fixedBase B).map g).hom element
    exact congrArg
      (fun morphism : (F.tangent.fixedBase B).obj N ⟶ (F.tangent.fixedBase B).obj N' =>
        morphism.hom element)
      ((F.tangent.fixedBase B).map_add (f := f) (g := g))

/-- The argument-induced scalar action makes the tangent functor linear. -/
instance tangentArgument_linear (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) :
    (F.tangentArgument hF B).Linear B.right := by
  apply (Functor.linear_iff _ _).2
  intro N scalar
  ext element
  rfl

/-- Changing to the argument-induced action preserves right exactness. -/
instance tangentArgument_preservesFiniteColimits (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) :
    PreservesFiniteColimits (F.tangentArgument hF B) := by
  let forgetModule := forget₂ (ModuleCat.{u} B.right) AddCommGrpCat.{u}
  letI : PreservesFiniteColimits (F.tangent.fixedBase B) := hF B
  letI : PreservesFiniteColimits (F.tangent.fixedBase B ⋙ forgetModule) :=
    comp_preservesFiniteColimits _ _
  let comparison : F.tangent.fixedBase B ⋙ forgetModule ≅
      F.tangentArgument hF B ⋙ forgetModule :=
    NatIso.ofComponents (fun N => Iso.refl _) (by intro N N' f; rfl)
  letI : PreservesFiniteColimits (F.tangentArgument hF B ⋙ forgetModule) :=
    preservesFiniteColimits_of_natIso comparison
  exact preservesFiniteColimits_of_reflects_of_preserves _ forgetModule

/-- The argument-action tangent object has the same carrier as the original tangent object. -/
theorem tangentArgument_obj (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right) :
    ((F.tangentArgument hF B).obj N : Type u) = F.tangentObj B N := sorry

/-- Scalar multiplication in `tangentArgument` is induced by the scalar endomorphism of `N`. -/
theorem tangentArgument_smul (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
    (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right)
    (b : B.right) (x : (F.tangentArgument hF B).obj N) :
    Eq.mp (F.tangentArgument_obj hF B N) (b • x) =
      (F.tangent.fixedBase B).map (b • 𝟙 N)
        (Eq.mp (F.tangentArgument_obj hF B N) x) := sorry

/-- The maps of `tangentArgument` agree pointwise with the original tangent maps. -/
theorem tangentArgument_map_apply (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) {N N' : ModuleCat.{u} B.right}
    (f : N ⟶ N') (x : (F.tangentArgument hF B).obj N) :
    Eq.mp (F.tangentArgument_obj hF B N') ((F.tangentArgument hF B).map f x) =
      (F.tangent.fixedBase B).map f
        (Eq.mp (F.tangentArgument_obj hF B N) x) := sorry

/-- The canonical tensor-to-tangent map is linear for the argument-induced action. -/
private theorem tensorToTangentArgument_map_smul (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right)
    (b : B.right) (x : F.tangentTensor.obj B N) :
    F.tensorToTangentApp B N (b • x) =
      @SMul.smul B.right (TangentArgumentCarrier F hF B N)
        (tangentArgumentCarrierSMul F hF B N) ((RingHom.id B.right) b)
        (F.tensorToTangentApp B N x) := sorry

/-- The canonical map `N ⊗[B] F(B) ⟶ TF(B, N)` is linear for the
argument-induced `B`-module structure on its target. -/
noncomputable def tensorToTangentArgument (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right) :
    F.tangentTensor.obj B N ⟶ (F.tangentArgument hF B).obj N :=
  -- Local instance justification (proof-local temporary data): `ModuleCat.ofHom` requires the explicit target additive-group datum on the argument-action carrier.
  letI := tangentArgumentCarrierAddCommGroup F hF B N
  -- Local instance justification (proof-local temporary data): `ModuleCat.ofHom` requires the explicit target scalar-action datum on the argument-action carrier.
  letI := tangentArgumentCarrierSMul F hF B N
  -- Local instance justification (proof-local temporary data): `ModuleCat.ofHom` requires the explicit target module datum on the argument-action carrier.
  letI := tangentArgumentCarrierModule F hF B N
  ModuleCat.ofHom {
    toFun := fun x ↦ F.tensorToTangentApp B N x
    map_add' := (F.tensorToTangentApp B N).hom.map_add
    map_smul' := tensorToTangentArgument_map_smul F hF B N }

/-- The re-bundled tensor comparison agrees pointwise with `tensorToTangentApp`. -/
theorem tensorToTangentArgument_apply (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right)
    (x : F.tangentTensor.obj B N) :
    Eq.mp (F.tangentArgument_obj hF B N) (F.tensorToTangentArgument hF B N x) =
      F.tensorToTangentApp B N x := sorry

/-- The canonical map `TF(B, B) ⊗[B] N ⟶ TF(B, N)` formed with the
argument-induced scalar action on `TF(B, B)`. -/
@[expose] noncomputable def tangentTensorComparison (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right) :
    (F.tangentArgument hF B).obj (ModuleCat.of B.right B.right) ⊗ N ⟶
      (F.tangentArgument hF B).obj N :=
  (β_ ((F.tangentArgument hF B).obj (ModuleCat.of B.right B.right)) N).hom ≫
    ModuleCat.tensorRightComparisonApp (F.tangentArgument hF B) N

/-- The tangent comparison is the general module-functor comparison after swapping factors. -/
theorem tangentTensorComparison_eq (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right) :
    F.tangentTensorComparison hF B N =
      (β_ ((F.tangentArgument hF B).obj (ModuleCat.of B.right B.right)) N).hom ≫
        ModuleCat.tensorRightComparisonApp (F.tangentArgument hF B) N := rfl

/-- The canonical comparison acts on pure tensors through the tangent map induced by `1 ↦ n`. -/
theorem tangentTensorComparison_tmul (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right)
    (x : (F.tangentArgument hF B).obj (ModuleCat.of B.right B.right)) (n : N) :
    F.tangentTensorComparison hF B N (x ⊗ₜ[B.right] n) =
      (F.tangentArgument hF B).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton B.right N n)) x := by
  change ModuleCat.tensorRightComparisonApp (F.tangentArgument hF B) N
    (n ⊗ₜ[B.right] x) = _
  exact ModuleCat.tensorRightComparisonApp_tmul (F.tangentArgument hF B) N n x

/-- For a finitely presented `B`-module `N`, the canonical map
`TF(B, B) ⊗[B] N ⟶ TF(B, N)` is an isomorphism. -/
theorem tangentTensorComparisonIsIso (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right)
    [Module.FinitePresentation B.right N] :
    IsIso (F.tangentTensorComparison hF B N) := by
  rw [tangentTensorComparison_eq]
  exact IsIso.comp_isIso' (Iso.isIso_hom (β_ _ _))
    (ModuleCat.isIso_tensorRightComparisonApp_of_finitePresentation
      (F.tangentArgument hF B) N)

end ModuleValuedFunctor
