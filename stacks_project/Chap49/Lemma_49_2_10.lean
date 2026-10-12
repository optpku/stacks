/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.BaseChange.Bijective
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u v

/- Lemma 49.2.10: if the quasi-finite homomorphism `A → B` is flat, then the
base-change map induces an isomorphism
`ω_{B/A} ⊗[B] B₁ → ω_{B₁/A₁}`. The tensor product is written with
`B₁` on the left, the canonical scalar-extension orientation in Lean. -/
@[stacks 0BVF] #check (Algebra.RelativeDualizingModule.baseChangeTensorOf_bijective_of_flat :
  ∀
    (A A₁ : Type u) (B' B B₁' B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing B'] [CommRing B]
    [CommRing B₁'] [CommRing B₁]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A₁ B₁'] [Algebra B₁' B₁] [Algebra A₁ B₁]
    [IsScalarTower A₁ B₁' B₁]
    [Algebra A A₁] [Algebra B' B₁'] [Algebra B B₁]
    [Algebra A B₁'] [IsScalarTower A B' B₁'] [IsScalarTower A A₁ B₁']
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [Algebra B' B₁] [IsScalarTower B' B B₁] [IsScalarTower B' B₁' B₁]
    [Module.Flat A B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A₁ B₁)
    [Module.Finite A B'] [Module.Finite A₁ B₁']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁))))
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' B₁').toLinearMap),
    Function.Bijective
      (Algebra.RelativeDualizingModule.baseChangeTensorOf A A₁ B' B B₁' B₁
        h_quasiFinite h_quasiFinite₁ h_open h_open₁ h_baseChange h_finiteModel))
