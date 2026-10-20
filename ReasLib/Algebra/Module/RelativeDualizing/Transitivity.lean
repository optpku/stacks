/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import ReasLib.Algebra.Module.RelativeDualizing.BaseChange

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.DualModule Algebra.RelativeDual TensorProduct TensorProduct.Right

universe u v w z

/-- The canonical forward comparison from the normalized finite-dual model to
the tensor product of two chosen relative dualizing modules. On pure tensors it
base-changes the second dual and inserts the unit in the first scalar extension. -/
def Algebra.RelativeDual.normalizationToSource
    (A B B' C C' : Type u)
    [CommRing A] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra B' C] [IsScalarTower B' B C]
    [Algebra B' C'] [Algebra A C'] [IsScalarTower A B' C']
    [Algebra C' C] [IsScalarTower B' C' C] [IsScalarTower A C' C]
    (h_quasiFiniteAB : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFiniteBC : Algebra.FiniteType.QuasiFinite B C)
    [Module.Finite A B'] [Module.Finite B' C'] [Module.Finite A C']
    (h_openB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_openC : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))) :
    C ⊗[C'] (Module.Dual B' C' ⊗[B'] Module.Dual A B') →ₗ[C]
      (Algebra.RelativeDualizingModule.of A B' B h_quasiFiniteAB h_openB ⊗[B]
        Algebra.RelativeDualizingModule.of B (B ⊗[B'] C') C h_quasiFiniteBC
          (Algebra.RelativeDual.baseChange_isOpenImmersion B' B C' C h_openC)) :=
  -- Local instance justification (defeq pin): the outer tensor lift needs the target `C'`-module induced by `algebraMap C' C`.
  letI : Module C'
      (Algebra.RelativeDualizingModule.of A B' B h_quasiFiniteAB h_openB ⊗[B]
        Algebra.RelativeDualizingModule.of B (B ⊗[B'] C') C h_quasiFiniteBC
          (Algebra.RelativeDual.baseChange_isOpenImmersion B' B C' C h_openC)) :=
    Module.compHom _ (algebraMap C' C)
  -- Local instance justification (defeq pin): the inner tensor lift needs the target `B'`-module induced by `algebraMap B' C'`.
  letI : Module B'
      (Algebra.RelativeDualizingModule.of A B' B h_quasiFiniteAB h_openB ⊗[B]
        Algebra.RelativeDualizingModule.of B (B ⊗[B'] C') C h_quasiFiniteBC
          (Algebra.RelativeDual.baseChange_isOpenImmersion B' B C' C h_openC)) :=
    Module.compHom _ (algebraMap B' C')
  let innerMap (c : C) :
      (Module.Dual B' C' ⊗[B'] Module.Dual A B') →ₗ[C']
        (Algebra.RelativeDualizingModule.of A B' B h_quasiFiniteAB h_openB ⊗[B]
          Algebra.RelativeDualizingModule.of B (B ⊗[B'] C') C h_quasiFiniteBC
            (Algebra.RelativeDual.baseChange_isOpenImmersion B' B C' C h_openC)) :=
    { toFun :=
        (_root_.TensorProduct.lift
            (LinearMap.mk₂ B' (fun g f ↦ TensorProduct.tmul B
                ((f ⊗ₜ[B'] (1 : B)) :
                  Algebra.RelativeDualizingModule.of A B' B h_quasiFiniteAB h_openB)
                ((Module.Dual.baseChange B g ⊗ₜ[(B ⊗[B'] C')] c) :
                  Algebra.RelativeDualizingModule.of B (B ⊗[B'] C') C h_quasiFiniteBC
                    (Algebra.RelativeDual.baseChange_isOpenImmersion B' B C' C h_openC)))
              sorry sorry sorry sorry) :
          (Module.Dual B' C' ⊗[B'] Module.Dual A B') →ₗ[B']
            (Algebra.RelativeDualizingModule.of A B' B h_quasiFiniteAB h_openB ⊗[B]
              Algebra.RelativeDualizingModule.of B (B ⊗[B'] C') C h_quasiFiniteBC
                (Algebra.RelativeDual.baseChange_isOpenImmersion B' B C' C h_openC)))
      map_add' := sorry
      map_smul' := sorry }
  { toFun :=
      _root_.TensorProduct.lift
        { toFun := innerMap
          map_add' := sorry
          map_smul' := sorry }
    map_add' := sorry
    map_smul' := sorry }

/-- The forward normalization comparison sends a pure tensor to the two
base-changed relative-dual factors in the chosen finite-open models. -/
theorem Algebra.RelativeDual.normalizationToSource_tmul
    (A B B' C C' : Type u)
    [CommRing A] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra B' C] [IsScalarTower B' B C]
    [Algebra B' C'] [Algebra A C'] [IsScalarTower A B' C']
    [Algebra C' C] [IsScalarTower B' C' C] [IsScalarTower A C' C]
    (h_quasiFiniteAB : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFiniteBC : Algebra.FiniteType.QuasiFinite B C)
    [Module.Finite A B'] [Module.Finite B' C'] [Module.Finite A C']
    (h_openB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_openC : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C))))
    (c : C) (g : Module.Dual B' C') (f : Module.Dual A B') :
    Algebra.RelativeDual.normalizationToSource A B B' C C' h_quasiFiniteAB
        h_quasiFiniteBC h_openB h_openC (c ⊗ₜ (g ⊗ₜ f)) =
      TensorProduct.tmul B (f ⊗ₜ[B'] (1 : B))
        (Module.Dual.baseChange B g ⊗ₜ[(B ⊗[B'] C')] c) := sorry

/-- The forward normalization comparison is bijective. Finiteness over the
Noetherian finite model supplies finite presentation, while the open immersion
`Spec B ⟶ Spec B'` supplies the flat base change used for the dual. -/
theorem Algebra.RelativeDual.normalizationToSource_bijective
    (A B B' C C' : Type u)
    [CommRing A] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra B' C] [IsScalarTower B' B C]
    [Algebra B' C'] [Algebra A C'] [IsScalarTower A B' C']
    [Algebra C' C] [IsScalarTower B' C' C] [IsScalarTower A C' C]
    (h_quasiFiniteAB : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFiniteBC : Algebra.FiniteType.QuasiFinite B C)
    [Module.Finite A B'] [Module.Finite B' C'] [Module.Finite A C']
    (h_openB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_openC : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))) :
    Function.Bijective (Algebra.RelativeDual.normalizationToSource A B B' C C'
      h_quasiFiniteAB h_quasiFiniteBC h_openB h_openC) := sorry

/-- The comparison from the tensor product of the two chosen models to the
normalized finite-dual model, obtained as the proof-independent chosen inverse
function of the explicit forward normalization map. -/
noncomputable def Algebra.RelativeDual.sourceToNormalization
    (A B B' C C' : Type u)
    [CommRing A] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra B' C] [IsScalarTower B' B C]
    [Algebra B' C'] [Algebra A C'] [IsScalarTower A B' C']
    [Algebra C' C] [IsScalarTower B' C' C] [IsScalarTower A C' C]
    (h_quasiFiniteAB : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFiniteBC : Algebra.FiniteType.QuasiFinite B C)
    [Module.Finite A B'] [Module.Finite B' C'] [Module.Finite A C']
    (h_openB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_openC : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))) :
    (Algebra.RelativeDualizingModule.of A B' B h_quasiFiniteAB h_openB ⊗[B]
      Algebra.RelativeDualizingModule.of B (B ⊗[B'] C') C h_quasiFiniteBC
        (Algebra.RelativeDual.baseChange_isOpenImmersion B' B C' C h_openC)) →ₗ[C]
      C ⊗[C'] (Module.Dual B' C' ⊗[B'] Module.Dual A B') :=
  let f := Algebra.RelativeDual.normalizationToSource A B B' C C'
    h_quasiFiniteAB h_quasiFiniteBC h_openB h_openC
  let h := Algebra.RelativeDual.normalizationToSource_bijective A B B' C C'
    h_quasiFiniteAB h_quasiFiniteBC h_openB h_openC
  LinearMap.inverse f (Function.invFun f)
    (Function.leftInverse_invFun h.1) (Function.rightInverse_invFun h.2)

/-- The source-to-normalization comparison is a left inverse to the explicit
forward normalization map. -/
theorem Algebra.RelativeDual.sourceToNormalization_normalizationToSource
    (A B B' C C' : Type u)
    [CommRing A] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra B' C] [IsScalarTower B' B C]
    [Algebra B' C'] [Algebra A C'] [IsScalarTower A B' C']
    [Algebra C' C] [IsScalarTower B' C' C] [IsScalarTower A C' C]
    (h_quasiFiniteAB : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFiniteBC : Algebra.FiniteType.QuasiFinite B C)
    [Module.Finite A B'] [Module.Finite B' C'] [Module.Finite A C']
    (h_openB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_openC : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C))))
    (x : C ⊗[C'] (Module.Dual B' C' ⊗[B'] Module.Dual A B')) :
    Algebra.RelativeDual.sourceToNormalization A B B' C C' h_quasiFiniteAB
        h_quasiFiniteBC h_openB h_openC
        (Algebra.RelativeDual.normalizationToSource A B B' C C' h_quasiFiniteAB
          h_quasiFiniteBC h_openB h_openC x) = x := sorry

/-- Composition of relative linear duals along a tower `A → B → C`. -/
def Algebra.RelativeDual.comp
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (g : Module.Dual B C) (f : Module.Dual A B) :
    Module.Dual A C :=
  f.comp (g.restrictScalars A)

/-- Composition with a fixed second relative dual sends zero to zero. -/
theorem Algebra.RelativeDual.comp_zero_right
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (g : Module.Dual B C) :
    Algebra.RelativeDual.comp A B C g 0 = 0 := sorry

/-- Composition with a fixed second relative dual preserves addition. -/
theorem Algebra.RelativeDual.comp_add_right
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (g : Module.Dual B C) (f₁ f₂ : Module.Dual A B) :
    Algebra.RelativeDual.comp A B C g (f₁ + f₂) =
      Algebra.RelativeDual.comp A B C g f₁ + Algebra.RelativeDual.comp A B C g f₂ := sorry

/-- Additive composition with a fixed element of the second relative dual. -/
def Algebra.RelativeDual.compAddHom
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (g : Module.Dual B C) :
    Module.Dual A B →+ Module.Dual A C where
  toFun := Algebra.RelativeDual.comp A B C g
  map_zero' := Algebra.RelativeDual.comp_zero_right A B C g
  map_add' := Algebra.RelativeDual.comp_add_right A B C g

/-- The additive composition homomorphism attached to zero is zero. -/
theorem Algebra.RelativeDual.compAddHom_zero
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    Algebra.RelativeDual.compAddHom A B C 0 = 0 := sorry

/-- The additive composition homomorphism preserves addition in its second-dual input. -/
theorem Algebra.RelativeDual.compAddHom_add
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (g₁ g₂ : Module.Dual B C) :
    Algebra.RelativeDual.compAddHom A B C (g₁ + g₂) =
      Algebra.RelativeDual.compAddHom A B C g₁ +
        Algebra.RelativeDual.compAddHom A B C g₂ := sorry

/-- Composition of relative duals as a map additive in both inputs. -/
def Algebra.RelativeDual.compBiadditive
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    Module.Dual B C →+ (Module.Dual A B →+ Module.Dual A C) where
  toFun := Algebra.RelativeDual.compAddHom A B C
  map_zero' := Algebra.RelativeDual.compAddHom_zero A B C
  map_add' := Algebra.RelativeDual.compAddHom_add A B C

/-- Composition of relative duals is balanced over the intermediate ring. -/
theorem Algebra.RelativeDual.compBiadditive_balance
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (b : B) (g : Module.Dual B C) (f : Module.Dual A B) :
    Algebra.RelativeDual.compBiadditive A B C (b • g) f =
      Algebra.RelativeDual.compBiadditive A B C g (b • f) := sorry

/-- The additive map induced by composition on the tensor product is linear over
the top ring. -/
theorem Algebra.RelativeDual.compTensor_smul
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (c : C) (x : Module.Dual B C ⊗[B] Module.Dual A B) :
    TensorProduct.liftAddHom (Algebra.RelativeDual.compBiadditive A B C)
        (Algebra.RelativeDual.compBiadditive_balance A B C) (c • x) =
      c • TensorProduct.liftAddHom (Algebra.RelativeDual.compBiadditive A B C)
        (Algebra.RelativeDual.compBiadditive_balance A B C) x := sorry

/-- The `C`-linear map on relative duals induced by composition
`Module.Dual A B × Module.Dual B C → Module.Dual A C`. -/
def Algebra.RelativeDual.compTensor
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (Module.Dual B C ⊗[B] Module.Dual A B) →ₗ[C] Module.Dual A C where
  toFun := TensorProduct.liftAddHom (Algebra.RelativeDual.compBiadditive A B C)
    (Algebra.RelativeDual.compBiadditive_balance A B C)
  map_add' := (TensorProduct.liftAddHom (Algebra.RelativeDual.compBiadditive A B C)
    (Algebra.RelativeDual.compBiadditive_balance A B C)).map_add
  map_smul' := Algebra.RelativeDual.compTensor_smul A B C

/-- Extension of the relative-dual composition map from `C` to a `C`-algebra `D`.
The reversed tensor order makes the extension-ring actions canonical. -/
def Algebra.RelativeDual.transitivityMap
    (A : Type u) (B : Type v) (C : Type w) (D : Type z)
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra C D] :
    D ⊗[C] (Module.Dual B C ⊗[B] Module.Dual A B) →ₗ[D]
      D ⊗[C] Module.Dual A C :=
  (Algebra.RelativeDual.compTensor A B C).baseChange D

/-- On pure tensors, the transitivity map is scalar extension of composition. -/
theorem Algebra.RelativeDual.transitivityMap_tmul
    (A : Type u) (B : Type v) (C : Type w) (D : Type z)
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra C D] (d : D) (g : Module.Dual B C) (f : Module.Dual A B) :
    Algebra.RelativeDual.transitivityMap A B C D (d ⊗ₜ (g ⊗ₜ f)) =
      d ⊗ₜ Algebra.RelativeDual.comp A B C g f := sorry

/-- The symmetry from a left scalar extension to the right-oriented tensor model,
linear for the extension-ring action on the target's right factor. -/
def Algebra.RelativeDual.scalarExtensionComm
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] :
    S ⊗[R] M →ₗ[S] M ⊗[R] S where
  toFun := _root_.TensorProduct.comm R S M
  map_add' := (_root_.TensorProduct.comm R S M).map_add
  map_smul' := sorry

/-- The scalar-extension symmetry exchanges the two factors of a pure tensor. -/
theorem Algebra.RelativeDual.scalarExtensionComm_tmul
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (s : S) (m : M) :
    Algebra.RelativeDual.scalarExtensionComm R S M (s ⊗ₜ m) = m ⊗ₜ s := sorry

/-- The transitivity map from the tensor product of chosen relative dualizing
modules for `A → B` and `B → C` to the chosen relative dualizing module for
`A → C`. -/
noncomputable def Algebra.RelativeDualizingModule.transitivityMapOf
    (A B B' C C' : Type u)
    [CommRing A] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra B' C] [IsScalarTower B' B C]
    [Algebra B' C'] [Algebra A C'] [IsScalarTower A B' C']
    [Algebra C' C] [IsScalarTower B' C' C] [IsScalarTower A C' C]
    (h_quasiFiniteAB : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFiniteBC : Algebra.FiniteType.QuasiFinite B C)
    [Module.Finite A B'] [Module.Finite B' C'] [Module.Finite A C']
    (h_openB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_openC : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))) :
    (Algebra.RelativeDualizingModule.of A B' B h_quasiFiniteAB h_openB ⊗[B]
        Algebra.RelativeDualizingModule.of B (B ⊗[B'] C') C h_quasiFiniteBC
          (Algebra.RelativeDual.baseChange_isOpenImmersion B' B C' C h_openC)) →ₗ[C]
      Algebra.RelativeDualizingModule.of A C' C
        (h_quasiFiniteAB.comp h_quasiFiniteBC) h_openC :=
  (Algebra.RelativeDual.scalarExtensionComm C' C (Module.Dual A C')).comp
    ((Algebra.RelativeDual.transitivityMap A B' C' C).comp
      (Algebra.RelativeDual.sourceToNormalization A B B' C C' h_quasiFiniteAB
        h_quasiFiniteBC h_openB h_openC))

/-- On normalized pure tensors, the chosen-model transitivity map is composition
of relative duals followed by scalar extension. -/
theorem Algebra.RelativeDualizingModule.transitivityMapOf_apply_normalizationToSource_tmul
    (A B B' C C' : Type u)
    [CommRing A] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra B' C] [IsScalarTower B' B C]
    [Algebra B' C'] [Algebra A C'] [IsScalarTower A B' C']
    [Algebra C' C] [IsScalarTower B' C' C] [IsScalarTower A C' C]
    (h_quasiFiniteAB : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFiniteBC : Algebra.FiniteType.QuasiFinite B C)
    [Module.Finite A B'] [Module.Finite B' C'] [Module.Finite A C']
    (h_openB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_openC : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C))))
    (c : C) (g : Module.Dual B' C') (f : Module.Dual A B') :
    Algebra.RelativeDualizingModule.transitivityMapOf A B B' C C'
        h_quasiFiniteAB h_quasiFiniteBC h_openB h_openC
        (Algebra.RelativeDual.normalizationToSource A B B' C C' h_quasiFiniteAB
          h_quasiFiniteBC h_openB h_openC (c ⊗ₜ (g ⊗ₜ f))) =
      Algebra.RelativeDual.comp A B' C' g f ⊗ₜ[C'] c := sorry
