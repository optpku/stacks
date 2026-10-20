module

public import ReasLib.Algebra.Module.RelativeDualizing
public import ReasLib.RingTheory.Kaehler.NoetherDifferent.AnnihilatorBaseChange

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.DualModule TensorProduct TensorProduct.Right

universe u v

namespace Algebra.RelativeDualizingModule

/-- Contract a tensor in `B ⊗[A] B` against an `A`-linear functional on its first
factor. -/
noncomputable def contractLeft (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (f : Module.Dual A B) :
    B ⊗[A] B →ₗ[A] B :=
  _root_.TensorProduct.lift
    (LinearMap.mk₂ A (fun b₁ b₂ ↦ algebraMap A B (f b₁) * b₂)
      sorry sorry sorry sorry)

/-- The finite-algebra pairing between the dual module and the annihilator of the
diagonal ideal, obtained by contraction in the first tensor factor. -/
noncomputable def finiteNoetherPairing (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] :
    Algebra.DualModule.of A B →ₗ[B]
      ((KaehlerDifferential.ideal A B).annihilator →ₗ[B] B) where
  toFun f :=
    { toFun := fun ξ ↦ contractLeft A B f ξ
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- Extend the finite-algebra pairing along `B' → B` in both arguments. -/
noncomputable def scalarExtensionNoetherPairing
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B] :
    (Algebra.DualModule.of A B' ⊗[B'] B) →ₗ[B]
      (((KaehlerDifferential.ideal A B').annihilator ⊗[B'] B) →ₗ[B] B) where
  toFun ω :=
    { toFun := fun η ↦
        _root_.TensorProduct.lift
          (LinearMap.mk₂ B' (fun f b ↦
            _root_.TensorProduct.lift
              (LinearMap.mk₂ B' (fun ξ c ↦
                algebraMap B' B (finiteNoetherPairing A B' f ξ) * b * c)
                sorry sorry sorry sorry)
              η)
            sorry sorry sorry sorry)
          ω
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- Scalar-extended contraction vanishes on the kernel of annihilator base change. -/
theorem annihilatorBaseChange_ker_le
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (ω : Algebra.DualModule.of A B' ⊗[B'] B) :
    LinearMap.ker (KaehlerDifferential.annihilatorBaseChange A B' B h_open) ≤
      LinearMap.ker (scalarExtensionNoetherPairing A B' B ω) := sorry

/-- Descend scalar-extended contraction through the annihilator base-change
equivalence. -/
noncomputable def descendedNoetherPairing
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (ω : Algebra.DualModule.of A B' ⊗[B'] B) :
    (KaehlerDifferential.ideal A B).annihilator →ₗ[B] B :=
  let relations : Submodule B
      ((KaehlerDifferential.ideal A B').annihilator ⊗[B'] B) :=
    LinearMap.ker (KaehlerDifferential.annihilatorBaseChange A B' B h_open)
  let contraction :
      (KaehlerDifferential.ideal A B').annihilator ⊗[B'] B →ₗ[B] B :=
    scalarExtensionNoetherPairing A B' B ω
  (relations.liftQ contraction
      (annihilatorBaseChange_ker_le A B' B h_open ω)).comp
    (KaehlerDifferential.annihilatorBaseChangeEquiv A B' B h_open).symm.toLinearMap

/-- Descended contraction agrees with scalar-extended contraction on the image of
annihilator base change. -/
theorem descendedNoetherPairing_apply
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (ω : Algebra.DualModule.of A B' ⊗[B'] B)
    (η : (KaehlerDifferential.ideal A B').annihilator ⊗[B'] B) :
    descendedNoetherPairing A B' B h_open ω
        (KaehlerDifferential.annihilatorBaseChange A B' B h_open η) =
      scalarExtensionNoetherPairing A B' B ω η := sorry

/-- The canonical pairing from a chosen-factorization relative dualizing module and
the annihilator of the diagonal ideal to the target algebra. -/
noncomputable def noetherPairing
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))) :
    RelativeDualizingModule.of A B' B h_quasiFinite h_open →ₗ[B]
      ((KaehlerDifferential.ideal A B).annihilator →ₗ[B] B) where
  toFun ω := descendedNoetherPairing A B' B h_open ω
  map_add' := sorry
  map_smul' := sorry

/-- On pure tensors, the canonical pairing is scalar extension of the finite-algebra
contraction pairing. -/
theorem noetherPairing_tmul
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (f : Algebra.DualModule.of A B') (b c : B)
    (ξ : (KaehlerDifferential.ideal A B').annihilator) :
    noetherPairing A B' B h_quasiFinite h_open (f ⊗ₜ[B'] b)
        (KaehlerDifferential.annihilatorBaseChange A B' B h_open (ξ ⊗ₜ[B'] c)) =
      algebraMap B' B (finiteNoetherPairing A B' f ξ) * b * c := sorry

/-- Agreement with the pure-tensor contraction formula uniquely determines the
canonical pairing. -/
theorem noetherPairing_unique
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (pairing : RelativeDualizingModule.of A B' B h_quasiFinite h_open →ₗ[B]
      ((KaehlerDifferential.ideal A B).annihilator →ₗ[B] B))
    (h_pairing : ∀ (f : Algebra.DualModule.of A B') (b c : B)
        (ξ : (KaehlerDifferential.ideal A B').annihilator),
      pairing (f ⊗ₜ[B'] b)
          (KaehlerDifferential.annihilatorBaseChange A B' B h_open (ξ ⊗ₜ[B'] c)) =
        algebraMap B' B (finiteNoetherPairing A B' f ξ) * b * c) :
    pairing = noetherPairing A B' B h_quasiFinite h_open := sorry

end Algebra.RelativeDualizingModule
