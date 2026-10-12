/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Isomorphisms
public import ReasLib.LinearAlgebra.TensorProduct.RightModule
public import ReasLib.RingTheory.Kaehler.NoetherDifferent.OpenImmersion

@[expose] public section

open AlgebraicGeometry
open scoped TensorProduct TensorProduct.Right

universe u v

namespace KaehlerDifferential

/-- The image of an element annihilating the diagonal ideal continues to annihilate
the diagonal ideal after extension along an affine open immersion. -/
theorem map_mem_annihilatorOfOpenImmersion
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (ξ : (ideal A B').annihilator) :
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B' B)
        (IsScalarTower.toAlgHom A B' B) ξ.1 ∈
      (ideal A B).annihilator := sorry

/-- The scalar-extension map from the annihilator of a diagonal ideal to the
annihilator after an affine open immersion. -/
noncomputable def annihilatorBaseChange
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))) :
    (ideal A B').annihilator ⊗[B'] B →ₗ[B] (ideal A B).annihilator where
  toFun η :=
    _root_.TensorProduct.lift
      (LinearMap.mk₂ B' (fun ξ c ↦ c •
          (⟨Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B' B)
              (IsScalarTower.toAlgHom A B' B) ξ.1,
            map_mem_annihilatorOfOpenImmersion A B' B h_open ξ⟩ :
            (ideal A B).annihilator))
        sorry sorry sorry sorry)
      η
  map_add' := sorry
  map_smul' := sorry

/-- The annihilator base-change map sends a pure tensor to the corresponding
scalar multiple of its image in `B ⊗[A] B`. -/
theorem annihilatorBaseChange_tmul
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (ξ : (ideal A B').annihilator) (c : B) :
    annihilatorBaseChange A B' B h_open (ξ ⊗ₜ[B'] c) = c •
      (⟨Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B' B)
          (IsScalarTower.toAlgHom A B' B) ξ.1,
        map_mem_annihilatorOfOpenImmersion A B' B h_open ξ⟩ :
        (ideal A B).annihilator) := sorry

/-- The quotient-valued inverse to annihilator base change, obtained from an arbitrary
preimage whose quotient class is independent of the choice. -/
noncomputable def annihilatorDescent
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))) :
    (ideal A B).annihilator →ₗ[B]
      (((ideal A B').annihilator ⊗[B'] B) ⧸
        LinearMap.ker (annihilatorBaseChange A B' B h_open)) where
  toFun ξ :=
    (LinearMap.ker (annihilatorBaseChange A B' B h_open)).mkQ
      (Function.invFun (annihilatorBaseChange A B' B h_open) ξ)
  map_add' := sorry
  map_smul' := sorry

/-- An element obtained by base change descends to its canonical class modulo the
kernel of the annihilator base-change map. -/
theorem annihilatorDescent_baseChange
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (η : (ideal A B').annihilator ⊗[B'] B) :
    annihilatorDescent A B' B h_open
        (annihilatorBaseChange A B' B h_open η) =
      (LinearMap.ker (annihilatorBaseChange A B' B h_open)).mkQ η := sorry

/-- The quotient by the kernel of annihilator base change is linearly equivalent to
the annihilator after extension along the affine open immersion. -/
noncomputable def annihilatorBaseChangeEquiv
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))) :
    (((ideal A B').annihilator ⊗[B'] B) ⧸
      LinearMap.ker (annihilatorBaseChange A B' B h_open)) ≃ₗ[B]
        (ideal A B).annihilator :=
  LinearEquiv.ofLinear
    ((LinearMap.ker (annihilatorBaseChange A B' B h_open)).liftQ
      (annihilatorBaseChange A B' B h_open) le_rfl)
    (annihilatorDescent A B' B h_open) sorry sorry

/-- The inverse annihilator comparison sends the image of a scalar-extended element
to its class modulo the kernel. -/
theorem annihilatorBaseChangeEquiv_symm_apply
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (η : (ideal A B').annihilator ⊗[B'] B) :
    (annihilatorBaseChangeEquiv A B' B h_open).symm
        (annihilatorBaseChange A B' B h_open η) =
      (LinearMap.ker (annihilatorBaseChange A B' B h_open)).mkQ η := sorry

end KaehlerDifferential
