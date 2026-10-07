module

public import ReasLib.RingTheory.Extension.Equiv
public import ReasLib.RingTheory.Extension.FirstOrder
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of Universal First-Order Thickenings

A universal first-order thickening admits a unique comparison map to every
square-zero extension in its testing universe.  Two thickenings universal in
a common universe containing both extension rings are therefore equivalent;
that equivalence is already unique under the one-sided comparison hypothesis.

@stack 04EF
-/

@[expose] public section

noncomputable section

open Algebra

namespace Algebra.Extension.FirstOrder.IsUniversal

universe u v w x

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable {P : Extension.{w} R S} {Q : Extension.{x} R S}

private theorem existsUniqueAlgHom_of_lift
    (hQsq : Q.ker ^ 2 = ⊥)
    (hlift : ∀ (J : Ideal Q.Ring), J ^ 2 = ⊥ →
      ∀ q : S →ₐ[R] Q.Ring ⧸ J,
        ∃! f : P.Ring →ₐ[R] Q.Ring,
          (Ideal.Quotient.mkₐ R J).comp f =
            q.comp (IsScalarTower.toAlgHom R P.Ring S)) :
    ∃! f : P.Ring →ₐ[R] Q.Ring,
      (IsScalarTower.toAlgHom R Q.Ring S).comp f =
        IsScalarTower.toAlgHom R P.Ring S := by
  let σQ : Q.Ring →ₐ[R] S := IsScalarTower.toAlgHom R Q.Ring S
  let J : Ideal Q.Ring := RingHom.ker σQ
  let eQ : (Q.Ring ⧸ J) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := σQ) Q.algebraMap_surjective
  let q : S →ₐ[R] (Q.Ring ⧸ J) := eQ.symm.toAlgHom
  have hJ : J ^ 2 = ⊥ := by
    change Q.ker ^ 2 = ⊥
    exact hQsq
  obtain ⟨f, hf, huniq⟩ := hlift J hJ q
  refine ⟨f, ?_, ?_⟩
  · apply AlgHom.ext
    intro p
    calc
      σQ (f p) = eQ (Ideal.Quotient.mk J (f p)) := by
        symm
        simpa only [eQ, J] using
          (Ideal.quotientKerAlgEquivOfSurjective_mk
            Q.algebraMap_surjective (f p))
      _ = eQ (q ((IsScalarTower.toAlgHom R P.Ring S) p)) :=
        congrArg eQ (DFunLike.congr_fun hf p)
      _ = (IsScalarTower.toAlgHom R P.Ring S) p := by
        change eQ (eQ.symm ((IsScalarTower.toAlgHom R P.Ring S) p)) = _
        exact eQ.apply_symm_apply _
  · intro g hg
    apply huniq g
    apply AlgHom.ext
    intro p
    apply eQ.injective
    calc
      eQ (Ideal.Quotient.mk J (g p)) = σQ (g p) := by
        simpa only [eQ, J] using
          (Ideal.quotientKerAlgEquivOfSurjective_mk
            Q.algebraMap_surjective (g p))
      _ = (IsScalarTower.toAlgHom R P.Ring S) p :=
        DFunLike.congr_fun hg p
      _ = eQ (q ((IsScalarTower.toAlgHom R P.Ring S) p)) := by
        change _ = eQ (eQ.symm ((IsScalarTower.toAlgHom R P.Ring S) p))
        exact (eQ.apply_symm_apply _).symm

/-- There is a unique algebra map from a universal first-order thickening to
a square-zero extension in its testing universe, commuting with the structure
maps to the common target. -/
@[stacks 04EF "unique comparison map to a square-zero extension"]
theorem existsUniqueAlgHom
    (hP : IsUniversal.{x} P) (hQsq : Q.ker ^ 2 = ⊥) :
    ∃! f : P.Ring →ₐ[R] Q.Ring,
      (IsScalarTower.toAlgHom R Q.Ring S).comp f =
        IsScalarTower.toAlgHom R P.Ring S :=
  existsUniqueAlgHom_of_lift hQsq fun J hJ q ↦ hP.existsUniqueLiftAt J hJ q

private theorem existsUniqueAlgHom_lifted
    (hP : IsUniversal.{max w x} P) (hQsq : Q.ker ^ 2 = ⊥) :
    ∃! f : P.Ring →ₐ[R] Q.Ring,
      (IsScalarTower.toAlgHom R Q.Ring S).comp f =
        IsScalarTower.toAlgHom R P.Ring S :=
  existsUniqueAlgHom_of_lift hQsq fun J hJ q ↦ hP.existsUniqueLift J hJ q

/-- Two algebra maps from a universal first-order thickening to a square-zero
extension are equal when both commute with the structure maps. -/
@[stacks 04EF "uniqueness of comparison maps"]
theorem algHom_eq
    (hP : IsUniversal.{x} P) (hQsq : Q.ker ^ 2 = ⊥)
    {f g : P.Ring →ₐ[R] Q.Ring}
    (hf : (IsScalarTower.toAlgHom R Q.Ring S).comp f =
      IsScalarTower.toAlgHom R P.Ring S)
    (hg : (IsScalarTower.toAlgHom R Q.Ring S).comp g =
      IsScalarTower.toAlgHom R P.Ring S) : f = g := by
  obtain ⟨h, hh, huniq⟩ := hP.existsUniqueAlgHom hQsq
  exact (huniq f hf).trans (huniq g hg).symm

private theorem endAlgHom_eq
    (hP : IsUniversal.{max w x} P)
    {f g : P.Ring →ₐ[R] P.Ring}
    (hf : (IsScalarTower.toAlgHom R P.Ring S).comp f =
      IsScalarTower.toAlgHom R P.Ring S)
    (hg : (IsScalarTower.toAlgHom R P.Ring S).comp g =
      IsScalarTower.toAlgHom R P.Ring S) : f = g := by
  let σP : P.Ring →ₐ[R] S := IsScalarTower.toAlgHom R P.Ring S
  let J : Ideal P.Ring := RingHom.ker σP
  let eP : (P.Ring ⧸ J) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := σP) P.algebraMap_surjective
  let q : S →ₐ[R] (P.Ring ⧸ J) := eP.symm.toAlgHom
  have hJ : J ^ 2 = ⊥ := by
    change P.ker ^ 2 = ⊥
    exact hP.squareZero
  obtain ⟨h, hh, huniq⟩ := hP.existsUniqueLift J hJ q
  have lift_spec (k : P.Ring →ₐ[R] P.Ring)
      (hk : σP.comp k = σP) :
      (Ideal.Quotient.mkₐ R J).comp k = q.comp σP := by
    apply AlgHom.ext
    intro p
    apply eP.injective
    calc
      eP (Ideal.Quotient.mk J (k p)) = σP (k p) := by
        simpa only [eP, J] using
          (Ideal.quotientKerAlgEquivOfSurjective_mk
            P.algebraMap_surjective (k p))
      _ = σP p := DFunLike.congr_fun hk p
      _ = eP (q (σP p)) := by
        change _ = eP (eP.symm (σP p))
        exact (eP.apply_symm_apply _).symm
  exact (huniq f (lift_spec f hf)).trans (huniq g (lift_spec g hg)).symm

/-- Universal first-order thickenings of the same algebra are equivalent as
extensions. -/
@[stacks 04EF "existence of the comparison equivalence"]
theorem existsEquiv
    (hP : IsUniversal.{max w x} P)
    (hQ : IsUniversal.{max w x} Q) :
    Nonempty (P.Equiv Q) := by
  obtain ⟨f, hf, _⟩ := existsUniqueAlgHom_lifted hP hQ.squareZero
  obtain ⟨g, hg, _⟩ := existsUniqueAlgHom_lifted hQ hP.squareZero
  have hgf : g.comp f = AlgHom.id R P.Ring := by
    apply endAlgHom_eq hP
    · rw [← AlgHom.comp_assoc, hg, hf]
    · simp
  have hfg : f.comp g = AlgHom.id R Q.Ring := by
    apply endAlgHom_eq hQ
    · rw [← AlgHom.comp_assoc, hf, hg]
    · simp
  let e : P.Ring ≃ₐ[R] Q.Ring := AlgEquiv.ofAlgHom f g hfg hgf
  exact ⟨⟨e, fun p ↦ DFunLike.congr_fun hf p⟩⟩

/-- The equivalence between two universal first-order thickenings is unique. -/
@[stacks 04EF "uniqueness of the comparison equivalence"]
theorem equiv_eq
    (hP : IsUniversal.{x} P) (hQsq : Q.ker ^ 2 = ⊥)
    (e f : P.Equiv Q) : e = f := by
  apply Extension.Equiv.ext
  apply AlgEquiv.ext
  have hef : e.toAlgEquiv.toAlgHom = f.toAlgEquiv.toAlgHom := by
    apply hP.algHom_eq hQsq
    · apply AlgHom.ext
      exact e.algebraMap_toAlgEquiv
    · apply AlgHom.ext
      exact f.algebraMap_toAlgEquiv
  intro p
  exact congrArg (fun h : P.Ring →ₐ[R] Q.Ring => h p) hef

/-- Equivalences between fixed universal first-order thickenings form a
subsingleton. -/
@[stacks 04EF "subsingleton comparison equivalences"]
theorem subsingletonEquiv
    (hP : IsUniversal.{x} P) (hQsq : Q.ker ^ 2 = ⊥) :
    Subsingleton (P.Equiv Q) :=
  ⟨hP.equiv_eq hQsq⟩

end Algebra.Extension.FirstOrder.IsUniversal
