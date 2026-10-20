module

public import stacks_project.Chap49.«49_2_3_1_BaseChange»
public import stacks_project.Chap49.Lemma_49_2_7_Product
public import stacks_project.Chap49.Lemma_49_4_3_ProjectiveTrace

@[expose] public section

noncomputable section

open AlgebraicGeometry
open scoped Algebra.DualModule Algebra.Product TensorProduct TensorProduct.Right

universe u

namespace Algebra.RelativeDualizingModule

/-- The spectrum map induced by the canonical self-algebra structure is an open immersion. -/
instance instIsOpenImmersionSpecMapIdentity (R : Type u) [CommRing R] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R R))) := sorry

/-- A finite factor of a product presentation of a flat base change is projective. -/
theorem leftFactorProjectiveOfBaseChange
    (A B A₁ C D : Type u)
    [CommRing A] [CommRing B] [CommRing A₁] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A A₁] [Algebra A₁ C] [Algebra A₁ D]
    [Algebra B (C × D)] [Algebra A (C × D)]
    [IsScalarTower A B (C × D)] [IsScalarTower A A₁ (C × D)]
    [Module.Flat A B] [IsNoetherianRing A₁] [Module.Finite A₁ C]
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B (C × D)).toLinearMap) :
    Module.Projective A₁ C := sorry

/-- The right factor of a product presentation of a quasi-finite base change is quasi-finite. -/
theorem rightFactorQuasiFiniteOfBaseChange
    (A B A₁ C D : Type u)
    [CommRing A] [CommRing B] [CommRing A₁] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A A₁] [Algebra A₁ C] [Algebra A₁ D]
    [Algebra B (C × D)] [Algebra A (C × D)]
    [IsScalarTower A B (C × D)] [IsScalarTower A A₁ (C × D)]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B (C × D)).toLinearMap) :
    Algebra.FiniteType.QuasiFinite A₁ D := sorry

/-- An element of a chosen presentation of `ω_{B/A}` is a trace element when every
Noetherian base change that decomposes as `C × D`, with `C` finite, sends it to the
finite-projective trace of `C` under base change followed by the product comparison. -/
def IsTraceElement
    (A B' B : Type u)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B] (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (τ : RelativeDualizingModule.of A B' B h_quasiFinite h_open) : Prop :=
  ∀ (A₁ C D D' : Type u)
    [CommRing A₁] [CommRing C] [CommRing D] [CommRing D']
    [IsNoetherianRing A₁] [IsNoetherianRing C] [IsNoetherianRing D]
    [Algebra A A₁] [Algebra A₁ C] [Algebra A₁ D'] [Algebra D' D]
    [Algebra A₁ D] [IsScalarTower A₁ D' D]
    [Algebra B' (C × D')] [Algebra B (C × D)]
    [Algebra A (C × D')] [IsScalarTower A B' (C × D')]
    [IsScalarTower A A₁ (C × D')]
    [Algebra A (C × D)] [IsScalarTower A B (C × D)]
    [IsScalarTower A A₁ (C × D)]
    [Algebra B' (C × D)] [IsScalarTower B' B (C × D)]
    [IsScalarTower B' (C × D') (C × D)]
    [Module.Finite A₁ C] [Module.Finite A₁ D']
    [h_openD : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap D' D)))]
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B (C × D)).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' (C × D')).toLinearMap),
    let hC : Algebra.FiniteType.QuasiFinite A₁ C :=
      Algebra.FiniteType.QuasiFinite.of_moduleFinite
    let hD : Algebra.FiniteType.QuasiFinite A₁ D :=
      rightFactorQuasiFiniteOfBaseChange A B A₁ C D h_quasiFinite h_baseChange
    let hCD := Algebra.FiniteType.QuasiFinite.prod hC hD
    (prodComparisonOf A₁ C C D' D hC hD
      (baseChangeOf A A₁ B' B (C × D') (C × D) h_quasiFinite hCD
        h_open inferInstance h_baseChange h_finiteModel τ)).1 =
      (@Algebra.finiteProjectiveTrace A₁ C _ _ _ _
        (leftFactorProjectiveOfBaseChange A B A₁ C D h_baseChange)) ⊗ₜ[C] (1 : C)

/-- The defining base-change/product equality supplied by an `IsTraceElement` witness. -/
theorem IsTraceElement.baseChange_fst
    (A B' B : Type u)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B] (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (τ : RelativeDualizingModule.of A B' B h_quasiFinite h_open)
    (hτ : IsTraceElement A B' B h_quasiFinite h_open τ)
    (A₁ C D D' : Type u)
    [CommRing A₁] [CommRing C] [CommRing D] [CommRing D']
    [IsNoetherianRing A₁] [IsNoetherianRing C] [IsNoetherianRing D]
    [Algebra A A₁] [Algebra A₁ C] [Algebra A₁ D'] [Algebra D' D]
    [Algebra A₁ D] [IsScalarTower A₁ D' D]
    [Algebra B' (C × D')] [Algebra B (C × D)]
    [Algebra A (C × D')] [IsScalarTower A B' (C × D')]
    [IsScalarTower A A₁ (C × D')]
    [Algebra A (C × D)] [IsScalarTower A B (C × D)]
    [IsScalarTower A A₁ (C × D)]
    [Algebra B' (C × D)] [IsScalarTower B' B (C × D)]
    [IsScalarTower B' (C × D') (C × D)]
    [Module.Finite A₁ C] [Module.Finite A₁ D']
    [h_openD : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap D' D)))]
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B (C × D)).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' (C × D')).toLinearMap) :
    let hC : Algebra.FiniteType.QuasiFinite A₁ C :=
      Algebra.FiniteType.QuasiFinite.of_moduleFinite
    let hD : Algebra.FiniteType.QuasiFinite A₁ D :=
      rightFactorQuasiFiniteOfBaseChange A B A₁ C D h_quasiFinite h_baseChange
    let hCD := Algebra.FiniteType.QuasiFinite.prod hC hD
    (prodComparisonOf A₁ C C D' D hC hD
      (baseChangeOf A A₁ B' B (C × D') (C × D) h_quasiFinite hCD
        h_open inferInstance h_baseChange h_finiteModel τ)).1 =
      (@Algebra.finiteProjectiveTrace A₁ C _ _ _ _
        (leftFactorProjectiveOfBaseChange A B A₁ C D h_baseChange)) ⊗ₜ[C] (1 : C) := sorry

end Algebra.RelativeDualizingModule
