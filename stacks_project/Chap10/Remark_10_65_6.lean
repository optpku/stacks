module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.RingHom.Fiber.Quotient
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Localization
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Quotient
import StacksCheckRecall

/-!
# Remark 10.65.6

@stack 05E0
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal.Quotient (eq_zero_iff_mem)
open scoped TensorProduct Algebra.TensorProduct.Right nonZeroDivisors

universe u v w

section

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime]
variable [AddCommGroup N] [Module S N]

local notation "Sbar" => S ⧸ p.map (algebraMap R S)
local notation "T" => Ideal.Fiber.quotientDenominators (R := R) (S := S) p
local notation "Nfiber" => (p.Fiber S) ⊗[S] N

/- Domain triage:
* `source-facing`: the two equalities in Remark 10.65.6 for associated primes of the fiber module.
* `core/canonical`: the owner theorem
  `associatedPrimesOfModule.Quotient.image_comap_eq` for contraction along a quotient map.
* `bridge/view`: the local `Sbar`-algebra structure on `p.Fiber S`, used only to state the
  source-facing fiber comparison for the canonical tensor model `Nfiber`.
-/

/- Remark 10.65.6, first equality: for the canonical fiber module modeling
`N ⊗_R κ(p)`, the comparison between associated primes over `S` and over `S ⧸ pS` is exactly the
specialization of the owner theorem
`associatedPrimesOfModule.Quotient.image_comap_eq` to the ideal `pS = p.map (algebraMap R S)` and
the `S`-module `Nfiber`. -/
@[stacks 05E0 "(1) quotient comparison"]
#check
  (associatedPrimesOfModule.Quotient.image_comap_eq (p.map (algebraMap R S)) :
    Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap R S))) ''
        associatedPrimesOfModule Sbar Nfiber =
      associatedPrimesOfModule S Nfiber)

/- Remark 10.65.6, second equality: for the same fiber module, the textbook associated primes
over `S ⧸ pS` agree with those over the fiber ring `κ(p) ⊗[R] S` after transporting them back to
ideals of `S`. -/
@[stacks 05E0 "(2) fiber-ring comparison"]
#check show
    Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap R S))) ''
        associatedPrimesOfModule Sbar Nfiber =
      Ideal.comap (algebraMap S (p.Fiber S)) ''
        associatedPrimesOfModule (p.Fiber S) Nfiber from by
  rw [← associatedPrimesOfModule_image_comap_eq_of_isLocalization
    (R := Sbar) (A := p.Fiber S) T (M := Nfiber)]
  ext I
  constructor
  · rintro ⟨K, ⟨J, hJ, rfl⟩, hKI⟩
    refine ⟨J, hJ, ?_⟩
    simpa [Ideal.comap_comap] using hKI
  · rintro ⟨J, hJ, hJmap⟩
    refine ⟨Ideal.comap (algebraMap Sbar (p.Fiber S)) J, ⟨J, hJ, rfl⟩, ?_⟩
    simpa [Ideal.comap_comap] using hJmap

end
