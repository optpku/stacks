/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.ScopedNS
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal

@[expose] public section

/-!
# Quotient presentations of residue-field fibers

This leaf complements mathlib's `Ideal.Fiber.algEquivQuotient`, whose source
is a localization of the target ring.  Here the source is the quotient by the
extended prime and then the image of the nonzerodivisors of the base quotient
is inverted.
-/

noncomputable section

universe u v w

open scoped TensorProduct Algebra.TensorProduct.Right nonZeroDivisors

namespace Ideal.Fiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime]

/-- Elements of the extension `pS` vanish in the residue-field fiber
`κ(p) ⊗[R] S`. -/
theorem algebraMap_eq_zero_of_mem_map {x : S}
    (hx : x ∈ p.map (algebraMap R S)) :
    algebraMap S (p.Fiber S) x = 0 := by
  apply (show p.map (algebraMap R S) ≤
      RingHom.ker (algebraMap S (p.Fiber S)) from ?_) hx
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  change algebraMap S (p.Fiber S) (algebraMap R S r) = 0
  rw [← IsScalarTower.algebraMap_apply R S (p.Fiber S)]
  change algebraMap p.ResidueField (p.Fiber S)
      (algebraMap R p.ResidueField r) = 0
  rw [Ideal.algebraMap_residueField_eq_zero.mpr hr, map_zero]

/-- The image in `S / pS` of the nonzerodivisors of `R / p`. -/
def quotientDenominators : Submonoid (S ⧸ p.map (algebraMap R S)) :=
  Algebra.algebraMapSubmonoid (S ⧸ p.map (algebraMap R S)) (nonZeroDivisors (R ⧸ p))

/-- The canonical `S / pS`-algebra structure on the residue-field fiber
`κ(p) ⊗[R] S`. -/
@[stacks 033A]
noncomputable instance quotientAlgebra :
    Algebra (S ⧸ p.map (algebraMap R S)) (p.Fiber S) :=
  (Ideal.Quotient.liftₐ (p.map (algebraMap R S))
    (Algebra.ofId S (p.Fiber S))
    (fun _ hx ↦ algebraMap_eq_zero_of_mem_map p hx)).toRingHom.toAlgebra

/-- Under `Ideal.Fiber.quotientAlgebra`, the class of `s : S` maps to the pure
tensor `1 ⊗ s` in the residue-field fiber. -/
@[simp]
theorem quotientAlgebraMap_mk (s : S) :
    algebraMap (S ⧸ p.map (algebraMap R S)) (p.Fiber S)
      (Ideal.Quotient.mk (p.map (algebraMap R S)) s) =
        1 ⊗ₜ[R] s := by
  rfl

/-- The quotient algebra map followed by the quotient map is the canonical
target-to-fiber map. -/
@[simp]
theorem quotientAlgebra_comp_quotientMap :
    (algebraMap (S ⧸ p.map (algebraMap R S)) (p.Fiber S)).comp
        (Ideal.Quotient.mk (p.map (algebraMap R S))) =
      algebraMap S (p.Fiber S) := by
  ext s
  exact quotientAlgebraMap_mk p s

section

variable (m : Ideal R) [m.IsMaximal]

/-- For a maximal ideal, base change of its quotient ring is the corresponding
residue-field fiber. -/
@[stacks 033A]
noncomputable def maximalTensorQuotientAlgEquiv :
    S ⊗[R] (R ⧸ m) ≃ₐ[S] m.Fiber S :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
    (Ideal.ResidueField.quotientAlgEquiv (K := R) m)).trans <|
      Algebra.TensorProduct.commRight R S m.ResidueField

/-- When `m` is maximal, the residue-field fiber is the quotient of `S` by
the extended ideal `mS`, as an `S`-algebra. -/
@[stacks 033A]
noncomputable def maximalQuotientAlgEquiv :
    (S ⧸ m.map (algebraMap R S)) ≃ₐ[S] m.Fiber S :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S m).trans <|
    maximalTensorQuotientAlgEquiv (R := R) (S := S) m

/-- The maximal-ideal quotient presentation sends the class of an element of
`S` to its canonical image in the residue-field fiber. -/
@[simp, stacks 033A]
theorem maximalQuotientAlgEquiv_apply_mk (s : S) :
    maximalQuotientAlgEquiv (R := R) (S := S) m
      (Ideal.Quotient.mk (m.map (algebraMap R S)) s) = algebraMap S (m.Fiber S) s := by
  simpa using (maximalQuotientAlgEquiv (R := R) (S := S) m).commutes s

/-- The inverse maximal-ideal quotient presentation sends the canonical image
of `s : S` in the residue-field fiber to its quotient class. -/
@[simp, stacks 033A]
theorem maximalQuotientAlgEquiv_symm_apply_algebraMap (s : S) :
    (maximalQuotientAlgEquiv (R := R) (S := S) m).symm
      (algebraMap S (m.Fiber S) s) =
        Ideal.Quotient.mk (m.map (algebraMap R S)) s := by
  apply (maximalQuotientAlgEquiv (R := R) (S := S) m).injective
  simp

/-- The canonical map from `S` to a residue-field fiber over a maximal ideal
is surjective. -/
@[stacks 033A]
theorem algebraMap_surjective_of_isMaximal :
    Function.Surjective (algebraMap S (m.Fiber S)) := by
  intro x
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
    ((maximalQuotientAlgEquiv (R := R) (S := S) m).symm x)
  refine ⟨s, ?_⟩
  rw [← maximalQuotientAlgEquiv_apply_mk, hs,
    (maximalQuotientAlgEquiv (R := R) (S := S) m).apply_symm_apply]

namespace Quotient

/-- The quotient-to-fiber algebra structure supplied by
`Ideal.Fiber.maximalQuotientAlgEquiv`.  The global
`Ideal.Fiber.quotientAlgebra` has the same mathematical map; this named owner
is for arguments that need that map definitionally pinned to the maximal
quotient presentation. -/
@[reducible, stacks 033A]
noncomputable def maximalQuotientAlgebra :
    Algebra (S ⧸ m.map (algebraMap R S)) (m.Fiber S) :=
  (Ideal.Fiber.maximalQuotientAlgEquiv (R := R) (S := S) m).toAlgHom.toAlgebra

/-- Under `maximalQuotientAlgebra`, the class of `s : S` maps to its canonical
image in the maximal residue-field fiber. -/
@[simp, stacks 033A]
theorem maximalQuotientAlgebraMap_mk (s : S) :
    letI : Algebra (S ⧸ m.map (algebraMap R S)) (m.Fiber S) :=
      maximalQuotientAlgebra (R := R) (S := S) m
    algebraMap (S ⧸ m.map (algebraMap R S)) (m.Fiber S)
      (Ideal.Quotient.mk (m.map (algebraMap R S)) s) =
        algebraMap S (m.Fiber S) s := by
  change maximalQuotientAlgEquiv (R := R) (S := S) m
      (Ideal.Quotient.mk (m.map (algebraMap R S)) s) = _
  exact maximalQuotientAlgEquiv_apply_mk (R := R) (S := S) m s

/-- The quotient presentation of a maximal fiber gives a canonical algebra
structure from the fiber to the quotient `S / mS`.  This reverse transport is
kept as a named definition rather than a global instance because the fiber
already carries its canonical `S`-algebra structure.  Consumers can opt into
this action through `open scoped Ideal.Fiber.Quotient`. -/
@[reducible, stacks 033A]
noncomputable def maximalAlgebra :
    Algebra (m.Fiber S) (S ⧸ m.map (algebraMap R S)) :=
  (Ideal.Fiber.maximalQuotientAlgEquiv (R := R) (S := S) m).symm.toAlgHom.toAlgebra

/-- The quotient `M / mS M`, regarded as a module over the maximal fiber through
`Ideal.Fiber.Quotient.maximalAlgebra`.  This is a named local transport, not a
global instance, since it chooses the reverse quotient presentation.  It is
available through `open scoped Ideal.Fiber.Quotient`. -/
@[reducible, stacks 033A]
noncomputable def maximalModule (M : Type w) [AddCommGroup M] [Module S M] :
    letI : Algebra (m.Fiber S) (S ⧸ m.map (algebraMap R S)) :=
      maximalAlgebra (R := R) (S := S) m
    Module (m.Fiber S)
      (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
  letI : Algebra (m.Fiber S) (S ⧸ m.map (algebraMap R S)) :=
    maximalAlgebra (R := R) (S := S) m
  Module.compHom _ (algebraMap (m.Fiber S) (S ⧸ m.map (algebraMap R S)))

/-- The transported maximal-fiber action on `M / mS M` restricts along
`S → m.Fiber S` to its original `S`-module action. -/
@[stacks 033A]
theorem maximalSourceScalarTower (M : Type w) [AddCommGroup M] [Module S M] :
    letI : Algebra (m.Fiber S) (S ⧸ m.map (algebraMap R S)) :=
      maximalAlgebra (R := R) (S := S) m
    letI : Module (m.Fiber S)
        (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
      maximalModule (R := R) (S := S) m M
    IsScalarTower S (m.Fiber S)
      (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) := by
  let J := m.map (algebraMap R S)
  let Abar := S ⧸ J
  let Q := M ⧸ (J • (⊤ : Submodule S M))
  letI : Algebra (m.Fiber S) Abar := maximalAlgebra (R := R) (S := S) m
  letI : Module (m.Fiber S) Q := maximalModule (R := R) (S := S) m M
  refine IsScalarTower.of_algebraMap_smul ?_
  intro s x
  refine Submodule.Quotient.induction_on (J • (⊤ : Submodule S M)) x ?_
  intro y
  change (algebraMap (m.Fiber S) Abar (algebraMap S (m.Fiber S) s)) •
      (Submodule.Quotient.mk y : Q) = s • (Submodule.Quotient.mk y : Q)
  rw [show algebraMap (m.Fiber S) Abar (algebraMap S (m.Fiber S) s) =
      Ideal.Quotient.mk J s from
    maximalQuotientAlgEquiv_symm_apply_algebraMap (R := R) (S := S) m s]
  rw [Module.Quotient.mk_smul_mk]
  exact Submodule.Quotient.mk_smul (J • (⊤ : Submodule S M)) s y

/-- The quotient presentation and its inverse give the scalar tower
`S / mS → m.Fiber S → M / mS M` after both algebra actions are definitionally
pinned to `Ideal.Fiber.maximalQuotientAlgEquiv`.  Use `quotientScalarTower`
when the ordinary global quotient algebra is sufficient. -/
@[stacks 033A]
theorem maximalQuotientScalarTower (M : Type w) [AddCommGroup M] [Module S M] :
    letI : Algebra (S ⧸ m.map (algebraMap R S)) (m.Fiber S) :=
      maximalQuotientAlgebra (R := R) (S := S) m
    letI : Algebra (m.Fiber S) (S ⧸ m.map (algebraMap R S)) :=
      maximalAlgebra (R := R) (S := S) m
    letI : Module (m.Fiber S)
        (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
      maximalModule (R := R) (S := S) m M
    IsScalarTower (S ⧸ m.map (algebraMap R S)) (m.Fiber S)
      (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) := by
  let Abar := S ⧸ m.map (algebraMap R S)
  let Q := M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))
  let e := maximalQuotientAlgEquiv (R := R) (S := S) m
  letI : Algebra Abar (m.Fiber S) := maximalQuotientAlgebra (R := R) (S := S) m
  letI : Algebra (m.Fiber S) Abar := maximalAlgebra (R := R) (S := S) m
  letI : Module (m.Fiber S) Q := maximalModule (R := R) (S := S) m M
  refine IsScalarTower.of_algebraMap_smul ?_
  intro a x
  change e.symm (e a) • x = a • x
  rw [e.symm_apply_apply]

/-- The canonical quotient algebra on a maximal residue-field fiber and its
reverse quotient action form a scalar tower on `M / mS M`.  This is the
ordinary downstream-facing version of `maximalQuotientScalarTower`: it uses
the global `Ideal.Fiber.quotientAlgebra` and can therefore be synthesized
after `open scoped Ideal.Fiber.Quotient`. -/
@[stacks 033A]
theorem quotientScalarTower (M : Type w) [AddCommGroup M] [Module S M] :
    letI : Algebra (m.Fiber S) (S ⧸ m.map (algebraMap R S)) :=
      maximalAlgebra (R := R) (S := S) m
    letI : Module (m.Fiber S)
        (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
      maximalModule (R := R) (S := S) m M
    IsScalarTower (S ⧸ m.map (algebraMap R S)) (m.Fiber S)
      (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) := by
  let Abar := S ⧸ m.map (algebraMap R S)
  let Q := M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))
  let e := maximalQuotientAlgEquiv (R := R) (S := S) m
  letI : Algebra (m.Fiber S) Abar := maximalAlgebra (R := R) (S := S) m
  letI : Module (m.Fiber S) Q := maximalModule (R := R) (S := S) m M
  have hmap : algebraMap Abar (m.Fiber S) = e.toRingEquiv.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    rw [quotientAlgebra_comp_quotientMap]
    ext s
    simpa using (e.commutes s).symm
  refine IsScalarTower.of_algebraMap_smul ?_
  intro a x
  change e.symm (algebraMap Abar (m.Fiber S) a) • x = a • x
  rw [hmap]
  change e.symm (e a) • x = a • x
  rw [e.symm_apply_apply]

/-- Tensoring an `S`-module with a maximal fiber is canonically its quotient
by the extended maximal ideal. -/
@[stacks 033A]
noncomputable def maximalTensorModuleEquiv (M : Type w) [AddCommGroup M] [Module S M] :
    letI : Algebra (m.Fiber S) (S ⧸ m.map (algebraMap R S)) :=
      maximalAlgebra (R := R) (S := S) m
    letI : Module (m.Fiber S)
        (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
      maximalModule (R := R) (S := S) m M
    (m.Fiber S) ⊗[S] M ≃ₗ[m.Fiber S]
      (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
  let Abar : Type v := S ⧸ m.map (algebraMap R S)
  letI : Algebra (m.Fiber S) Abar := maximalAlgebra (R := R) (S := S) m
  letI : Module (m.Fiber S) (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
    maximalModule (R := R) (S := S) m M
  letI : IsScalarTower S (m.Fiber S)
      (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
    maximalSourceScalarTower (R := R) (S := S) m M
  let eChange : (m.Fiber S) ⊗[S] M ≃ₗ[S] (Abar ⊗[S] M) :=
    TensorProduct.congr
      ((Ideal.Fiber.maximalQuotientAlgEquiv (R := R) (S := S) m).symm.toLinearEquiv)
      (LinearEquiv.refl S M)
  let eQuot : (Abar ⊗[S] M) ≃ₗ[Abar]
      (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
    (TensorProduct.quotTensorEquivQuotSMul M (m.map (algebraMap R S))).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  (eChange.trans (LinearEquiv.restrictScalars S eQuot)).extendScalarsOfSurjective
    (Ideal.Fiber.algebraMap_surjective_of_isMaximal (R := R) (S := S) m)

/-- `maximalTensorModuleEquiv` sends a pure tensor to the corresponding scalar
multiple of the quotient class. -/
@[simp, stacks 033A]
theorem maximalTensorModuleEquiv_apply_tmul (M : Type w) [AddCommGroup M] [Module S M]
    (a : m.Fiber S) (x : M) :
    letI : Algebra (m.Fiber S) (S ⧸ m.map (algebraMap R S)) :=
      maximalAlgebra (R := R) (S := S) m
    letI : Module (m.Fiber S)
        (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
      maximalModule (R := R) (S := S) m M
    maximalTensorModuleEquiv (R := R) (S := S) m M (a ⊗ₜ[S] x) =
      (algebraMap (m.Fiber S) (S ⧸ m.map (algebraMap R S)) a) •
        (Submodule.Quotient.mk x : M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) := by
  let Abar := S ⧸ m.map (algebraMap R S)
  let Q := M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))
  letI : Algebra (m.Fiber S) Abar := maximalAlgebra (R := R) (S := S) m
  letI : Module (m.Fiber S) Q := maximalModule (R := R) (S := S) m M
  let e := maximalTensorModuleEquiv (R := R) (S := S) m M
  have hOne : e ((1 : m.Fiber S) ⊗ₜ[S] x) =
      (Submodule.Quotient.mk x : Q) := by
    simp [e, maximalTensorModuleEquiv]
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, hOne]
  rfl

/-- The inverse quotient presentation sends a quotient representative to the
pure tensor with unit fiber factor. -/
@[simp, stacks 033A]
theorem maximalTensorModuleEquiv_symm_apply_mk (M : Type w) [AddCommGroup M] [Module S M]
    (x : M) :
    letI : Algebra (m.Fiber S) (S ⧸ m.map (algebraMap R S)) :=
      maximalAlgebra (R := R) (S := S) m
    letI : Module (m.Fiber S)
        (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
      maximalModule (R := R) (S := S) m M
    (maximalTensorModuleEquiv (R := R) (S := S) m M).symm
      (Submodule.Quotient.mk x : M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) =
        (1 : m.Fiber S) ⊗ₜ[S] x := by
  let Abar := S ⧸ m.map (algebraMap R S)
  let Q := M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))
  letI : Algebra (m.Fiber S) Abar := maximalAlgebra (R := R) (S := S) m
  letI : Module (m.Fiber S) Q := maximalModule (R := R) (S := S) m M
  let e := maximalTensorModuleEquiv (R := R) (S := S) m M
  apply e.injective
  rw [e.apply_symm_apply]
  have h : e ((1 : m.Fiber S) ⊗ₜ[S] x) =
      (Submodule.Quotient.mk x : Q) := by
    simpa only [map_one, one_smul] using maximalTensorModuleEquiv_apply_tmul
      (R := R) (S := S) m M (1 : m.Fiber S) x
  exact h.symm

/-- On the quotient module, the transported maximal-fiber scalar coming from
`s : S` agrees with the original `S`-scalar action. -/
@[simp, stacks 033A]
theorem maximalModule_smul_algebraMap (M : Type w) [AddCommGroup M] [Module S M]
    (s : S) (x : M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :
    letI : Algebra (m.Fiber S) (S ⧸ m.map (algebraMap R S)) :=
      maximalAlgebra (R := R) (S := S) m
    letI : Module (m.Fiber S)
        (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
      maximalModule (R := R) (S := S) m M
    ((algebraMap S (m.Fiber S) s) • x :
      M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) = s • x := by
  let Abar := S ⧸ m.map (algebraMap R S)
  let Q := M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))
  letI : Algebra (m.Fiber S) Abar := maximalAlgebra (R := R) (S := S) m
  letI : Module (m.Fiber S) Q := maximalModule (R := R) (S := S) m M
  letI : IsScalarTower S (m.Fiber S) Q :=
    maximalSourceScalarTower (R := R) (S := S) m M
  exact IsScalarTower.algebraMap_smul (m.Fiber S) s x

/-- `maximalTensorModuleEquiv` carries multiplication by the image of `s : S`
to multiplication by the quotient class of `s`. -/
@[simp, stacks 033A]
theorem maximalTensorModuleEquiv_smul_algebraMap (M : Type w) [AddCommGroup M] [Module S M]
    (s : S) (x : (m.Fiber S) ⊗[S] M) :
    letI : Algebra (m.Fiber S) (S ⧸ m.map (algebraMap R S)) :=
      maximalAlgebra (R := R) (S := S) m
    letI : Module (m.Fiber S)
        (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) :=
      maximalModule (R := R) (S := S) m M
    maximalTensorModuleEquiv (R := R) (S := S) m M
      ((algebraMap S (m.Fiber S) s) • x) =
        (Ideal.Quotient.mk (m.map (algebraMap R S)) s) •
          maximalTensorModuleEquiv (R := R) (S := S) m M x := by
  let J := m.map (algebraMap R S)
  let Abar := S ⧸ J
  let Q := M ⧸ (J • (⊤ : Submodule S M))
  letI : Algebra (m.Fiber S) Abar := maximalAlgebra (R := R) (S := S) m
  letI : Module (m.Fiber S) Q := maximalModule (R := R) (S := S) m M
  let e := maximalTensorModuleEquiv (R := R) (S := S) m M
  rw [map_smul, maximalModule_smul_algebraMap]
  refine Submodule.Quotient.induction_on (J • (⊤ : Submodule S M)) (e x) ?_
  intro y
  rw [Module.Quotient.mk_smul_mk]
  exact (Submodule.Quotient.mk_smul (J • (⊤ : Submodule S M)) s y).symm

/-- Flatness of the maximal-fiber tensor module descends to the quotient presentation of the
module.  This is the neutral bridge used by fiberwise flatness criteria; it packages the ring
equivalence `S / mS ≃ₐ[S] m.Fiber S`, the transported quotient-module action, and the tensor
equivalence into one reusable statement. -/
@[stacks 033A "maximal-fiber flatness transport"]
theorem flat_quotient_of_flat_tensor (M : Type w) [AddCommGroup M] [Module S M]
    (hflat : Module.Flat (m.Fiber S) ((m.Fiber S) ⊗[S] M)) :
    Module.Flat (S ⧸ m.map (algebraMap R S))
      (M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))) := by
  let Abar := S ⧸ m.map (algebraMap R S)
  let Q := M ⧸ (m.map (algebraMap R S) • (⊤ : Submodule S M))
  let eRing := maximalQuotientAlgEquiv (R := R) (S := S) m
  letI : Algebra (m.Fiber S) Abar := maximalAlgebra (R := R) (S := S) m
  letI : Module (m.Fiber S) Q := maximalModule (R := R) (S := S) m M
  letI : IsScalarTower Abar (m.Fiber S) Q :=
    quotientScalarTower (R := R) (S := S) m M
  let eModule := maximalTensorModuleEquiv (R := R) (S := S) m M
  letI : Module.Flat (m.Fiber S) ((m.Fiber S) ⊗[S] M) := hflat
  letI : Module.Flat (m.Fiber S) Q := Module.Flat.of_linearEquiv eModule.symm
  have hmap : algebraMap Abar (m.Fiber S) = eRing.toRingEquiv.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    rw [quotientAlgebra_comp_quotientMap]
    ext s
    simpa using (eRing.commutes s).symm
  letI : Module.Flat Abar (m.Fiber S) := RingHom.flat_algebraMap_iff.mp <|
    RingHom.Flat.of_bijective (by
      rw [hmap]
      exact eRing.bijective)
  exact Module.Flat.trans Abar (m.Fiber S) Q

end Quotient

/-- The closed fiber of a local `R`-algebra has its canonical quotient presentation,
viewed as an `R`-algebra.  This is the scalar restriction of
`Ideal.Fiber.maximalQuotientAlgEquiv` in the direction from the fiber to the quotient. -/
@[stacks 031E]
noncomputable def closedQuotientAlgEquiv [IsLocalRing R] :
    (IsLocalRing.maximalIdeal R).Fiber S ≃ₐ[R]
      S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S) :=
  (maximalQuotientAlgEquiv (R := R) (S := S) (IsLocalRing.maximalIdeal R)).symm
    |>.restrictScalars R

/-- The closed-fiber quotient presentation sends the canonical image of a target element to
its quotient class. -/
@[simp, stacks 031E]
theorem closedQuotientAlgEquiv_apply_algebraMap [IsLocalRing R] (s : S) :
    closedQuotientAlgEquiv (R := R) (S := S)
      (algebraMap S ((IsLocalRing.maximalIdeal R).Fiber S) s) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) s := by
  exact maximalQuotientAlgEquiv_symm_apply_algebraMap
    (R := R) (S := S) (IsLocalRing.maximalIdeal R) s

/-- The inverse closed-fiber quotient presentation sends a quotient representative to its
canonical image in the fiber. -/
@[simp, stacks 031E]
theorem closedQuotientAlgEquiv_symm_apply_mk [IsLocalRing R] (s : S) :
    (closedQuotientAlgEquiv (R := R) (S := S)).symm
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) s) =
        algebraMap S ((IsLocalRing.maximalIdeal R).Fiber S) s := by
  exact maximalQuotientAlgEquiv_apply_mk
    (R := R) (S := S) (IsLocalRing.maximalIdeal R) s

/-- The kernel of the canonical map to a residue-field fiber over a maximal
ideal is the extended maximal ideal. -/
theorem ker_algebraMap_of_isMaximal :
    RingHom.ker (algebraMap S (m.Fiber S)) = m.map (algebraMap R S) := by
  ext s
  constructor
  · intro hs
    have h := congrArg
      (maximalQuotientAlgEquiv (R := R) (S := S) m).symm hs
    simpa only [map_zero, maximalQuotientAlgEquiv_symm_apply_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem] using h
  · exact algebraMap_eq_zero_of_mem_map m

/-- A fiber over a maximal ideal is local when its quotient presentation is a
proper quotient of a local target ring. -/
theorem isLocalRing_of_isMaximal_of_map_ne_top [IsLocalRing S]
    (hmap : m.map (algebraMap R S) ≠ ⊤) :
    IsLocalRing (m.Fiber S) := by
  letI : Nontrivial (S ⧸ m.map (algebraMap R S)) :=
    Ideal.Quotient.nontrivial_iff.mpr hmap
  letI : Nontrivial (m.Fiber S) :=
    (maximalQuotientAlgEquiv (R := R) (S := S) m).symm.toEquiv.nontrivial
  exact IsLocalRing.of_surjective' (algebraMap S (m.Fiber S))
    (algebraMap_surjective_of_isMaximal (R := R) (S := S) m)

end

section

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- The closed fiber of a local homomorphism of local rings is local. -/
theorem isLocalRing_of_isLocalHom :
    IsLocalRing ((IsLocalRing.maximalIdeal R).Fiber S) := by
  apply isLocalRing_of_isMaximal_of_map_ne_top
  exact (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne

/-- The closed fiber of a local homomorphism of local rings is canonically a
local ring. -/
noncomputable instance closedFiberIsLocalRing :
    IsLocalRing ((IsLocalRing.maximalIdeal R).Fiber S) :=
  isLocalRing_of_isLocalHom (R := R) (S := S)

end

/-- The quotient-base-changed fiber presentation recovers `κ(p) ⊗[R] S` as
an algebra over `S / pS`. -/
noncomputable def quotientTensorAlgEquiv :
    (S ⧸ p.map (algebraMap R S)) ⊗[R ⧸ p] p.ResidueField ≃ₐ[
      S ⧸ p.map (algebraMap R S)] p.Fiber S :=
  let eRing :
      (S ⧸ p.map (algebraMap R S)) ⊗[R ⧸ p] p.ResidueField ≃+* p.Fiber S :=
    (Algebra.TensorProduct.commRight (R ⧸ p)
      (S ⧸ p.map (algebraMap R S)) p.ResidueField).toRingEquiv.trans
      ((Algebra.TensorProduct.congr
          (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField] p.ResidueField)
          (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p)).trans
        (Algebra.TensorProduct.cancelBaseChange R (R ⧸ p) p.ResidueField
          p.ResidueField S)).toRingEquiv
  { toRingEquiv := eRing
    commutes' := by
      intro x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp [eRing] }

/-- Localizing `S / pS` at the image of the nonzerodivisors of `R / p`
recovers the residue-field fiber `κ(p) ⊗[R] S`. -/
@[stacks 033A]
noncomputable def quotientLocalizationAlgEquiv :
    Localization (quotientDenominators (R := R) (S := S) p) ≃ₐ[
      S ⧸ p.map (algebraMap R S)] p.Fiber S :=
  ((Localization.tensorLeftAlgEquiv
      (nonZeroDivisors (R ⧸ p)) (S ⧸ p.map (algebraMap R S))).symm.trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl :
          (S ⧸ p.map (algebraMap R S)) ≃ₐ[S ⧸ p.map (algebraMap R S)]
            (S ⧸ p.map (algebraMap R S)))
        (IsLocalization.algEquiv (nonZeroDivisors (R ⧸ p))
          (Localization (nonZeroDivisors (R ⧸ p))) p.ResidueField))).trans
    (quotientTensorAlgEquiv p)

/-- The residue-field fiber is canonically the localization of `S / pS` at
`Ideal.Fiber.quotientDenominators`. -/
noncomputable instance quotientIsLocalization :
    IsLocalization (quotientDenominators (R := R) (S := S) p) (p.Fiber S) :=
  IsLocalization.isLocalization_of_algEquiv _ (quotientLocalizationAlgEquiv p)

/-- A residue-field fiber inherits Noetherianity from its target ring. -/
theorem isNoetherianRing [IsNoetherianRing S] :
    IsNoetherianRing (p.Fiber S) := by
  exact IsLocalization.isNoetherianRing
    (quotientDenominators (R := R) (S := S) p) (p.Fiber S) inferInstance

/-- A residue-field fiber over a Noetherian target ring is Noetherian. -/
noncomputable instance fiberIsNoetherianRing [IsNoetherianRing S] :
    IsNoetherianRing (p.Fiber S) :=
  isNoetherianRing (R := R) (S := S) p

/-- The quotient-localization presentation agrees with its target algebra map
on an element of `S / pS`. -/
@[simp]
theorem quotientLocalizationAlgEquiv_apply_algebraMap
    (x : S ⧸ p.map (algebraMap R S)) :
    quotientLocalizationAlgEquiv p
      (algebraMap (S ⧸ p.map (algebraMap R S))
        (Localization (quotientDenominators (R := R) (S := S) p)) x) =
      algebraMap (S ⧸ p.map (algebraMap R S)) (p.Fiber S) x :=
  (quotientLocalizationAlgEquiv p).commutes x

/-- The quotient-localization presentation sends the class of `s : S` to the
pure tensor `1 ⊗ s` in the residue-field fiber. -/
@[simp]
theorem quotientLocalizationAlgEquiv_apply_mk (s : S) :
    quotientLocalizationAlgEquiv p
      (algebraMap (S ⧸ p.map (algebraMap R S))
        (Localization (quotientDenominators (R := R) (S := S) p))
          (Ideal.Quotient.mk (p.map (algebraMap R S)) s)) =
      1 ⊗ₜ[R] s := by
  rw [quotientLocalizationAlgEquiv_apply_algebraMap]
  exact quotientAlgebraMap_mk p s

/-- The quotient-localization presentation of a residue-field fiber agrees
with the canonical target-to-fiber map on elements of `S`. -/
theorem quotientLocalizationAlgEquiv_comp_quotientMap :
    let I : Ideal S := p.map (algebraMap R S)
    let T : Submonoid (S ⧸ I) := quotientDenominators (R := R) (S := S) p
    (quotientLocalizationAlgEquiv p).toRingHom.comp
        ((algebraMap (S ⧸ I) (Localization T)).comp (Ideal.Quotient.mk I)) =
      algebraMap S (p.Fiber S) := by
  dsimp
  ext s
  change quotientLocalizationAlgEquiv p
      (algebraMap (S ⧸ p.map (algebraMap R S))
        (Localization (quotientDenominators (R := R) (S := S) p))
          (Ideal.Quotient.mk (p.map (algebraMap R S)) s)) =
    algebraMap S (p.Fiber S) s
  rw [quotientLocalizationAlgEquiv_apply_mk]
  rfl

end Ideal.Fiber

/-! The quotient presentation has a noncanonical reverse scalar action.  Keep
it out of global search, but let consumers opt into the coherent reverse
algebra, module, and scalar-tower instances in one place.  The forward
`Ideal.Fiber.quotientAlgebra` remains the ordinary global quotient action. -/
scoped[Ideal.Fiber.Quotient] attribute [instance 100]
  Ideal.Fiber.Quotient.maximalAlgebra
  Ideal.Fiber.Quotient.maximalModule
  Ideal.Fiber.Quotient.maximalSourceScalarTower
  Ideal.Fiber.Quotient.quotientScalarTower
