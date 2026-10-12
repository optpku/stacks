/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Comparison
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Transport of modules across ring direct-limit presentations

This leaf packages the scalar actions needed to transport a base-changed
module through an equivalence from a ring direct-limit presentation to another
ring. The actions are selected locally because they depend on the chosen stage
and ring equivalence, rather than being canonical global instances.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y

noncomputable section

namespace Ring.DirectLimit.Module.Transport

variable {I : Type u} [Preorder I]
variable {R : I → Type v} [∀ i, CommRing (R i)]
variable (f : ∀ i j, i ≤ j → R i →+* R j)

/-- The module action obtained by restricting scalars along a direct-limit
ring equivalence is compatible with the original codomain action. -/
@[stacks 05N7 "direct-limit module transport"]
theorem module_isScalarTower
    {T : Type w} [CommRing T]
    (e : Ring.DirectLimit R (fun i j h ↦ f i j h) ≃+* T)
    {M : Type x} [AddCommGroup M] [_root_.Module T M] :
    letI : Algebra T (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
      e.symm.toRingHom.toAlgebra
    letI : _root_.Module (Ring.DirectLimit R (fun i j h ↦ f i j h)) M :=
      _root_.Module.compHom M e.toRingHom
    IsScalarTower T (Ring.DirectLimit R (fun i j h ↦ f i j h)) M := sorry

/-- Transport a base-change equivalence over a ring direct limit to the
codomain of a chosen ring equivalence. -/
@[stacks 05N7 "direct-limit module transport"]
noncomputable def baseChangeEquiv
    {T : Type w} [CommRing T]
    (e : Ring.DirectLimit R (fun i j h ↦ f i j h) ≃+* T) (i : I)
    {M_i : Type y} [AddCommGroup M_i] [_root_.Module (R i) M_i]
    {M : Type x} [AddCommGroup M] [_root_.Module T M]
    (eM :
      letI : Algebra (R i) (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i
      letI : _root_.Module (Ring.DirectLimit R (fun i j h ↦ f i j h)) M :=
        _root_.Module.compHom M e.toRingHom
      Ring.DirectLimit R (fun i j h ↦ f i j h) ⊗[R i] M_i ≃ₗ[
        Ring.DirectLimit R (fun i j h ↦ f i j h)] M) :
    letI : Algebra (R i) T := (Ring.DirectLimit.toLimitHom R f e i).toAlgebra
    T ⊗[R i] M_i ≃ₗ[T] M :=
  letI : Algebra (R i) (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
    Ring.DirectLimit.Algebra.stageAlgebra f i
  letI : Algebra (R i) T := (Ring.DirectLimit.toLimitHom R f e i).toAlgebra
  letI : _root_.Module (Ring.DirectLimit R (fun i j h ↦ f i j h)) M :=
    _root_.Module.compHom M e.toRingHom
  letI : Algebra T (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
    e.symm.toRingHom.toAlgebra
  letI : IsScalarTower (R i) T (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
    Ring.DirectLimit.toLimitHom_inverse_isScalarTower R f e i
  letI : IsScalarTower T (Ring.DirectLimit R (fun i j h ↦ f i j h)) M :=
    module_isScalarTower f e
  let eDT : Ring.DirectLimit R (fun i j h ↦ f i j h) ≃ₐ[T] T :=
    Ring.DirectLimit.Comparison.algebraEquiv f e
  let eTensor :
      Ring.DirectLimit R (fun i j h ↦ f i j h) ⊗[R i] M_i ≃ₗ[T] T ⊗[R i] M_i :=
    TensorProduct.AlgebraTensorModule.congr eDT.toLinearEquiv (LinearEquiv.refl (R i) M_i)
  eTensor.symm.trans (eM.restrictScalars T)

/-- The transported base-change equivalence sends a pure tensor to the given
direct-limit equivalence evaluated after applying the inverse ring
equivalence to its scalar. -/
@[stacks 05N7 "direct-limit module transport"]
theorem baseChangeEquiv_tmul
    {T : Type w} [CommRing T]
    (e : Ring.DirectLimit R (fun i j h ↦ f i j h) ≃+* T) (i : I)
    {M_i : Type y} [AddCommGroup M_i] [_root_.Module (R i) M_i]
    {M : Type x} [AddCommGroup M] [_root_.Module T M]
    (eM :
      letI : Algebra (R i) (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i
      letI : _root_.Module (Ring.DirectLimit R (fun i j h ↦ f i j h)) M :=
        _root_.Module.compHom M e.toRingHom
      Ring.DirectLimit R (fun i j h ↦ f i j h) ⊗[R i] M_i ≃ₗ[
        Ring.DirectLimit R (fun i j h ↦ f i j h)] M)
    (t : T) (m : M_i) :
    letI : Algebra (R i) (Ring.DirectLimit R (fun i j h ↦ f i j h)) :=
      Ring.DirectLimit.Algebra.stageAlgebra f i
    letI : Algebra (R i) T := (Ring.DirectLimit.toLimitHom R f e i).toAlgebra
    letI : _root_.Module (Ring.DirectLimit R (fun i j h ↦ f i j h)) M :=
      _root_.Module.compHom M e.toRingHom
    baseChangeEquiv f e i eM (t ⊗ₜ[R i] m) = eM (e.symm t ⊗ₜ[R i] m) := sorry

end Ring.DirectLimit.Module.Transport
