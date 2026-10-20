/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import stacks_project.Chap10.Lemma_10_127_13.TailApproximation
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Limit
public import ReasLib.Algebra.Module.FinitePresentation.RingEquiv
public import ReasLib.RingTheory.DirectLimit.Module.FinitePresentation

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w uR uS uM uN

section

variable {R : Type uR} {S : Type uS} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [Module S M]

/-- Helper for Lemma 10.127.13: the tail transition modules are the standard cancel-base-change
modules obtained by extending scalars from the fixed descended stage. -/
private noncomputable def tail_module_transition_baseChange
    (A : DirectedLocalHomApproximation f) (i₀ : A.Λ)
    {M₀ : Type uS} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    (j k : Set.Ici i₀) (hjk : j ≤ k) :
    let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
    let _ : Module (A.SStage i₀) (A.SStage j.1) := inferInstance
    let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.targetMap i₀ k.1 k.2).toAlgebra
    let _ : Module (A.SStage i₀) (A.SStage k.1) := inferInstance
    let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.targetMap j.1 k.1 hjk).toAlgebra
    A.SStage k.1 ⊗[A.SStage j.1] (A.SStage j.1 ⊗[A.SStage i₀] M₀) ≃ₗ[A.SStage k.1]
      A.SStage k.1 ⊗[A.SStage i₀] M₀ :=
  let _ : Algebra (A.SStage i₀) (A.SStage j.1) := (A.targetMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A.SStage i₀) (A.SStage k.1) := (A.targetMap i₀ k.1 k.2).toAlgebra
  let _ : Algebra (A.SStage j.1) (A.SStage k.1) := (A.targetMap j.1 k.1 hjk).toAlgebra
  let _ : Module (A.SStage i₀) (A.SStage j.1) := inferInstance
  let _ : Module (A.SStage i₀) (A.SStage k.1) := inferInstance
  let _ : IsScalarTower (A.SStage i₀) (A.SStage j.1) (A.SStage k.1) :=
    Ring.DirectLimit.Algebra.Approximation.Hom.targetMap_isScalarTower
      A.toApproximation j.2 hjk
  -- Proof comment: tensoring once from `A.SStage i₀` to `A.SStage j.1` and then again to
  -- `A.SStage k.1` collapses to the single base change to `A.SStage k.1`.
  TensorProduct.AlgebraTensorModule.cancelBaseChange
    (A.SStage i₀) (A.SStage j.1) (A.SStage k.1) (A.SStage k.1) M₀

/-- Helper for Lemma 10.127.13: transport the descended direct-limit module equivalence across
the target-colimit ring equivalence to obtain an `S`-linear equivalence. -/
@[stacks 00QX "target-colimit module transport"]
theorem targetColimit_transport_descended_module_equiv
    (A : DirectedLocalHomApproximation f)
    (i₀ : A.Λ)
    {M₀ : Type uS} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    (eM :
      let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.targetMap i j h)
      let _ : Algebra (A.SStage i₀) D :=
        (Ring.DirectLimit.of A.SStage (fun i j h ↦ A.targetMap i j h) i₀).toAlgebra
      let _ : Module D M := Module.compHom M A.targetColimit.toRingHom
      D ⊗[A.SStage i₀] M₀ ≃ₗ[D] M) :
    let _ : Algebra (A.SStage i₀) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom A i₀).toAlgebra
    Nonempty (S ⊗[A.SStage i₀] M₀ ≃ₗ[S] M) := sorry

/-- Helper for Lemma 10.127.13: once a stage module has been descended to one target stage of the
ring approximation, the remaining source-faithful step is to restrict to the tail and define each
later stage by scalar extension from that fixed descended module. -/
@[stacks 00QX "tail module approximation"]
theorem tail_module_system_from_descended_stage
    (A : DirectedLocalHomApproximation.{uR, uS, max uR uS} f)
    (hA : DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A)
    (i₀ : A.Λ)
    {M₀ : Type uS} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    [Module.FinitePresentation (A.SStage i₀) M₀]
    (eM :
      let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.targetMap i j h)
      let _ : Algebra (A.SStage i₀) D :=
        (Ring.DirectLimit.of A.SStage (fun i j h ↦ A.targetMap i j h) i₀).toAlgebra
      let _ : Module D M := Module.compHom M A.targetColimit.toRingHom
      D ⊗[A.SStage i₀] M₀ ≃ₗ[D] M) :
    Nonempty
      (DirectedLocalHomApproximation.Module.{uR, uS, uM, uS, max uR uS} f M) := sorry

-- Proof sketch: first approximate the local map `R → S` by a directed system of local maps whose
-- source stages are essentially of finite type over `ℤ` and whose target stages are essentially
-- of finite type over the source stages. Then descend a finite presentation matrix for `M` to a
-- sufficiently large target stage, define the stage modules by cokernels of the descended
-- matrices, and use finite presentation to obtain the base-change isomorphisms between stages and
-- after passage to the colimit.

end
