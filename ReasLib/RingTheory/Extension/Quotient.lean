module

public import ReasLib.RingTheory.Extension.OfSurjective
public import ReasLib.RingTheory.Extension.Section
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebra Extensions Defined by Quotient Maps

Canonical quotients are packaged as algebra extensions. For a quotient of an
existing extension, the original chosen section descends to the quotient.
The companion API exposes structure maps, sections, kernels, and square-zero
specializations without unfolding the extension constructors.

@stack 04EB
-/

@[expose] public section

noncomputable section

open Algebra

namespace Ideal.Quotient

universe u v

variable (R : Type u) {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

/-- The algebra extension represented by the quotient map `A → A/I`. -/
@[stacks 04EB "quotient algebra extension"]
noncomputable def extension (I : Ideal A) : Algebra.Extension R (A ⧸ I) :=
  Algebra.Extension.ofSurjective (mkₐ R I) (mkₐ_surjective R I)

/-- The structure map of the quotient extension is the canonical quotient
map. -/
@[simp, stacks 04EB "quotient extension structure map"]
theorem extension_toAlgHom (I : Ideal A) :
    IsScalarTower.toAlgHom R (extension R I).Ring (A ⧸ I) = mkₐ R I := by
  exact Algebra.Extension.toAlgHom_ofSurjective _ _

/-- The kernel of the quotient extension is the defining ideal. -/
@[simp, stacks 04EB "quotient extension kernel"]
theorem extension_ker (I : Ideal A) :
    (extension R I).ker = I := by
  change RingHom.ker (mkₐ R I).toRingHom = I
  rw [mkₐ_toRingHom, Ideal.mk_ker]

/-- A quotient extension has square-zero kernel when its defining ideal has
square zero. -/
@[stacks 04EB "square-zero quotient extension"]
theorem extension_square_zero (I : Ideal A) (hI : I ^ 2 = ⊥) :
    (extension R I).ker ^ 2 = ⊥ := by
  rw [extension_ker]
  exact hI

end Ideal.Quotient

namespace Algebra.Extension.Quotient

universe u v w

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- The map to the target induced by quotienting an extension's source by an
ideal contained in its kernel. -/
@[stacks 04EB "quotient of an extension source"]
noncomputable def toAlgHom (P : Algebra.Extension.{w} R S) (I : Ideal P.Ring)
    (hI : I ≤ P.ker) : P.Ring ⧸ I →ₐ[R] S :=
  Ideal.Quotient.liftₐ I (IsScalarTower.toAlgHom R P.Ring S) hI

/-- The map induced by quotienting an extension's source remains
surjective. -/
@[stacks 04EB "quotient extension map is surjective"]
theorem toAlgHom_surjective (P : Algebra.Extension.{w} R S) (I : Ideal P.Ring)
    (hI : I ≤ P.ker) : Function.Surjective (toAlgHom P I hI) := by
  intro s
  refine ⟨Ideal.Quotient.mk I (P.σ s), ?_⟩
  change algebraMap P.Ring S (P.σ s) = s
  simp

/-- The kernel of the induced quotient map is the image of the original
extension kernel. -/
@[simp, stacks 04EB "kernel of a quotient extension map"]
theorem ker_toAlgHom (P : Algebra.Extension.{w} R S) (I : Ideal P.Ring)
    (hI : I ≤ P.ker) :
    RingHom.ker (toAlgHom P I hI).toRingHom = P.ker.map (Ideal.Quotient.mk I) := by
  simpa [toAlgHom, Ideal.Quotient.liftₐ] using
    (Ideal.ker_quotient_lift
      (IsScalarTower.toAlgHom R P.Ring S).toRingHom hI)

/-- The extension obtained by quotienting an extension's source by an ideal
contained in its kernel. -/
@[stacks 04EB "quotient extension"]
noncomputable def extension (P : Algebra.Extension.{w} R S) (I : Ideal P.Ring)
    (hI : I ≤ P.ker) : Algebra.Extension R S :=
  Algebra.Extension.ofSection (toAlgHom P I hI)
    (fun s ↦ Ideal.Quotient.mk I (P.σ s)) fun s ↦ by
      change algebraMap P.Ring S (P.σ s) = s
      simp

/-- The chosen section of a quotient extension is the image of the original
extension's section. -/
@[simp, stacks 04EB "quotient extension section"]
theorem extension_σ (P : Algebra.Extension.{w} R S) (I : Ideal P.Ring)
    (hI : I ≤ P.ker) (s : S) :
    (extension P I hI).σ s = Ideal.Quotient.mk I (P.σ s) := by
  rfl

/-- The structure map of a quotient extension is its induced quotient map. -/
@[simp, stacks 04EB "quotient extension structure map"]
theorem extension_toAlgHom (P : Algebra.Extension.{w} R S) (I : Ideal P.Ring)
    (hI : I ≤ P.ker) :
    IsScalarTower.toAlgHom R (extension P I hI).Ring S = toAlgHom P I hI := by
  rfl

/-- The kernel of a quotient extension is the image of the original
extension kernel. -/
@[simp, stacks 04EB "kernel of a quotient extension"]
theorem extension_ker (P : Algebra.Extension.{w} R S) (I : Ideal P.Ring)
    (hI : I ≤ P.ker) :
    (extension P I hI).ker = P.ker.map (Ideal.Quotient.mk I) := by
  exact ker_toAlgHom P I hI

/-- Quotienting the source of a square-zero extension by an ideal in its
kernel again gives a square-zero extension. -/
@[stacks 04EB "square-zero quotient extension"]
theorem extension_square_zero (P : Algebra.Extension.{w} R S) (I : Ideal P.Ring)
    (hI : I ≤ P.ker) (hsq : P.ker ^ 2 = ⊥) :
    (extension P I hI).ker ^ 2 = ⊥ := by
  rw [extension_ker]
  calc
    (P.ker.map (Ideal.Quotient.mk I)) ^ 2 =
        Ideal.map (Ideal.Quotient.mk I) (P.ker ^ 2) := by
      symm
      exact Ideal.map_pow (Ideal.Quotient.mk I) P.ker 2
    _ = ⊥ := by simp [hsq]

end Algebra.Extension.Quotient
