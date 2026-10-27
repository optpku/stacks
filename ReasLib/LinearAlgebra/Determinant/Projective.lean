/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants of finite-projective modules

The free-module determinant is extended to finite-projective modules through a split finite-free
presentation. The presentation is an implementation choice only: the public API exposes its
specification and independence, so downstream statements use `projectiveDet` rather than a chosen
presentation.

@stack 0FJF
-/

@[expose] public section

noncomputable section

universe u v w

namespace LinearMap

variable {R : Type u} [CommRing R]

/-- A split finite-free presentation of a finite-projective module. -/
@[stacks 0FJF "split finite-free presentation data"]
structure SplitFreePresentation (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] where
  rank : ℕ
  pi : (Fin rank → R) →ₗ[R] M
  iota : M →ₗ[R] Fin rank → R
  pi_comp_iota : pi.comp iota = LinearMap.id

variable {M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
  [Module.Finite R N] [Module.Projective R N]

/-- Finite projectivity supplies a split finite-free presentation. -/
@[stacks 0FJF "finite-projective split finite-free presentation"]
theorem nonempty_splitFreePresentation (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Nonempty (SplitFreePresentation R M) := by
  obtain ⟨n, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact ⟨⟨n, p, i, hpi⟩⟩
-- Proof strategy: unpack `Module.Finite.exists_comp_eq_id_of_projective R M` and package its
-- finite rank, projection, section, and split equation into `SplitFreePresentation`.

/-- The chosen presentation used by `projectiveDet`; use its specification rather than inspecting
the choice. -/
@[stacks 0FJF "chosen split finite-free presentation"]
noncomputable def splitFreePresentation (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    SplitFreePresentation R M :=
  let h := Module.Finite.exists_comp_eq_id_of_projective R M
  { rank := h.choose
    pi := h.choose_spec.choose
    iota := h.choose_spec.choose_spec.choose
    pi_comp_iota := h.choose_spec.choose_spec.choose_spec.2.2 }

/-- The endomorphism of the chosen free module induced by an endomorphism of `M`. -/
@[stacks 0FJF "lift of a projective endomorphism to a split free presentation"]
def SplitFreePresentation.lift
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (p : SplitFreePresentation R M) (f : M →ₗ[R] M) :
    (Fin p.rank → R) →ₗ[R] Fin p.rank → R :=
  (LinearMap.id - p.iota ∘ₗ p.pi) + p.iota ∘ₗ f ∘ₗ p.pi

/-- The determinant of a finite-projective endomorphism, computed from the chosen presentation. -/
@[stacks 0FJF "determinant of a finite-projective endomorphism"]
noncomputable def projectiveDet (f : M →ₗ[R] M) : R :=
  LinearMap.det ((splitFreePresentation R M).lift f)

/-- The chosen presentation satisfies the split relation used by `projectiveDet`. -/
@[stacks 0FJF "chosen split presentation equation"]
theorem splitFreePresentation_spec (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    (splitFreePresentation R M).pi.comp (splitFreePresentation R M).iota = LinearMap.id :=
  (splitFreePresentation R M).pi_comp_iota
-- Proof strategy: unfold `splitFreePresentation` and project the split equation from the nested
-- `Classical.choose_spec` fields of `Module.Finite.exists_comp_eq_id_of_projective`.

/-- The determinant of the lift is independent of the chosen split finite-free presentation. -/
private theorem det_id_add_comp_coordinates {m n : ℕ}
    (a : (Fin m → R) →ₗ[R] (Fin n → R)) (b : (Fin n → R) →ₗ[R] (Fin m → R)) :
    LinearMap.det (LinearMap.id + a ∘ₗ b) =
      LinearMap.det (LinearMap.id + b ∘ₗ a) := by
  rw [← det_toMatrix', ← det_toMatrix']
  simp only [map_add, toMatrix'_id, toMatrix'_comp]
  exact Matrix.det_one_add_mul_comm _ _

/-- The split lift is the identity plus a map factoring through the projective module. -/
theorem SplitFreePresentation.lift_eq_id_add
    (p : SplitFreePresentation R M) (f : M →ₗ[R] M) :
    p.lift f = LinearMap.id + p.iota ∘ₗ (f - LinearMap.id) ∘ₗ p.pi := by
  apply LinearMap.ext
  intro x
  simp only [SplitFreePresentation.lift, add_apply, sub_apply, comp_apply, id_apply, map_sub]
  abel

/-- The determinant of the lift is independent of the chosen split finite-free presentation. -/
@[stacks 0FJF "presentation independence of the projective determinant"]
theorem det_lift_independent
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (p q : SplitFreePresentation R M) (f : M →ₗ[R] M) :
    LinearMap.det (p.lift f) = LinearMap.det (q.lift f) := by
  let a := p.iota ∘ₗ (f - LinearMap.id) ∘ₗ q.pi
  let b := q.iota ∘ₗ p.pi
  have hp : ∀ x : M, p.pi (p.iota x) = x :=
    fun x ↦ congrArg (fun h : M →ₗ[R] M ↦ h x) p.pi_comp_iota
  have hq : ∀ x : M, q.pi (q.iota x) = x :=
    fun x ↦ congrArg (fun h : M →ₗ[R] M ↦ h x) q.pi_comp_iota
  have hab : a ∘ₗ b = p.iota ∘ₗ (f - LinearMap.id) ∘ₗ p.pi := by
    ext x
    simp only [a, b, comp_apply, hq]
  have hba : b ∘ₗ a = q.iota ∘ₗ (f - LinearMap.id) ∘ₗ q.pi := by
    ext x
    simp only [a, b, comp_apply, hp]
  rw [p.lift_eq_id_add, q.lift_eq_id_add, ← hab, ← hba]
  exact det_id_add_comp_coordinates a b
-- Proof strategy: stabilize the two free presentations on their direct sum, express the two lifts
-- as complementary block endomorphisms, and use `LinearMap.det_one_add_comp_comm` twice together
-- with `p.pi_comp_iota` and `q.pi_comp_iota`.

/-- `projectiveDet` agrees with the determinant computed from any chosen presentation. -/
@[stacks 0FJF "projective determinant from any split presentation"]
theorem projectiveDet_of_presentation
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (p : SplitFreePresentation R M) (f : M →ₗ[R] M) :
    projectiveDet f = LinearMap.det (p.lift f) :=
  det_lift_independent (splitFreePresentation R M) p f

/-- Changing coordinates by a linear equivalence preserves the finite-projective determinant.
The transported presentation is constructed with explicit maps in both directions. -/
theorem projectiveDet_conj (f : M →ₗ[R] M) (e : M ≃ₗ[R] N) :
    projectiveDet (e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap) = projectiveDet f := by
  let p := splitFreePresentation R M
  have hp : ∀ x : M, p.pi (p.iota x) = x :=
    fun x ↦ congrArg (fun h : M →ₗ[R] M ↦ h x) p.pi_comp_iota
  let q : SplitFreePresentation R N :=
    { rank := p.rank
      pi := e.toLinearMap ∘ₗ p.pi
      iota := p.iota ∘ₗ e.symm.toLinearMap
      pi_comp_iota := by
        apply LinearMap.ext
        intro x
        simp [comp_apply, hp] }
  rw [projectiveDet_of_presentation q, projectiveDet_of_presentation p]
  congr 1
  apply LinearMap.ext
  intro x
  simp [SplitFreePresentation.lift, q, comp_apply]
-- Proof strategy: unfold `projectiveDet` and apply `det_lift_independent` to the chosen
-- `splitFreePresentation R M` and `p`.

/-- The split lift of `1 + a ∘ₗ b` has the standard block form on the chosen free modules. -/
@[stacks 0FJF "split lift of one plus a composite"]
theorem lift_add_comp
    (pM : SplitFreePresentation R M) (pN : SplitFreePresentation R N)
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    pN.lift (1 + a ∘ₗ b) =
      1 + (pN.iota ∘ₗ a ∘ₗ pM.pi) ∘ₗ (pM.iota ∘ₗ b ∘ₗ pN.pi) := by
  have hsplit : ∀ x : M, pM.pi (pM.iota x) = x :=
    fun x ↦ congrArg (fun h : M →ₗ[R] M ↦ h x) pM.pi_comp_iota
  apply LinearMap.ext
  intro x
  simp only [SplitFreePresentation.lift, add_apply, sub_apply, comp_apply,
    Module.End.one_apply, id_apply, map_add, hsplit]
  abel
-- Proof strategy: unfold `SplitFreePresentation.lift`, distribute composition over addition, and
-- reassociate compositions until `pM.pi_comp_iota` and `pN.pi_comp_iota` reduce the cross terms.

/-- The finite-projective Weinstein–Aronszajn determinant identity. -/
@[stacks 0FJF "Weinstein-Aronszajn identity for finite-projective modules"]
theorem projectiveDet_id_add_comp
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    projectiveDet (1 + a ∘ₗ b) = projectiveDet (1 + b ∘ₗ a) := by
  rw [projectiveDet_of_presentation (splitFreePresentation R N),
    projectiveDet_of_presentation (splitFreePresentation R M), lift_add_comp, lift_add_comp]
  exact det_id_add_comp_coordinates _ _
-- Proof strategy: compute both sides using arbitrary chosen presentations, rewrite their lifts by
-- `lift_add_comp`, and apply the free-module identity `LinearMap.det_one_add_comp_comm` to the two
-- rectangular lifted maps.

/-- In the finite-free case, `projectiveDet` is the ordinary free-module determinant. -/
@[stacks 0FJF "projective determinant agrees with the free determinant"]
theorem projectiveDet_eq_det_of_free
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] [Module.Free R M]
    (f : M →ₗ[R] M) : projectiveDet f = LinearMap.det f := by
  classical
  nontriviality R
  let e := (Module.finBasis R M).equivFun
  let p : SplitFreePresentation R M :=
    ⟨Module.finrank R M, e.symm.toLinearMap, e.toLinearMap, by
      ext x
      exact e.symm_apply_apply x⟩
  rw [projectiveDet_of_presentation p]
  have hlift : p.lift f = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap := by
    ext x
    simp [SplitFreePresentation.lift, p]
  rw [hlift]
  exact det_conj f e
-- Proof strategy: use a finite basis to form the split presentation with `pi` and `iota` inverse;
-- apply `projectiveDet_of_presentation`, simplify its lift to the conjugate of `f`, and use
-- determinant invariance under the basis equivalence.

/-- The projective determinant of the identity endomorphism is one. -/
@[simp, stacks 0FJF "projective determinant of the identity"]
theorem projectiveDet_id
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    projectiveDet (LinearMap.id : M →ₗ[R] M) = 1 := by
  rw [projectiveDet, SplitFreePresentation.lift_eq_id_add]
  simp
-- Proof strategy: compute with `splitFreePresentation R M`; its lift of the identity simplifies to
-- the identity by `splitFreePresentation_spec`, then apply `LinearMap.det_id`.

end LinearMap

end
