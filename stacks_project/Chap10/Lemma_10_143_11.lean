/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.Quotient
public import ReasLib.RingTheory.Ideal.Cotangent.Equiv

/-!
# Etale lifting across square-zero extensions

@stack 05YT

The source condition `J = I ⊗[A] B` is represented by an equivalence between
the quotient-level tensor model of the source kernel cotangent and the target
kernel cotangent.  This file retains that source-facing lifting criterion; the
kernel, quotient, and cotangent constructions remain with their canonical
owners.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace RingHom

section


variable {Aprime : Type u} {A : Type v} {Bprime : Type w} {B : Type x}
variable [CommRing Aprime] [CommRing A] [CommRing Bprime] [CommRing B]
variable (g : Aprime →+* Bprime) (qA : Aprime →+* A) (qB : Bprime →+* B) (f : A →+* B)

/-- A commutative square sends the kernel of its upper-left quotient map into
the kernel of its lower-right quotient map. -/
theorem ker_le_comap_algebraMap_of_comp_eq_comp
    (hcomm : qB.comp g = f.comp qA) :
    letI : Algebra Aprime Bprime := g.toAlgebra
    RingHom.ker qA ≤
      Ideal.comap (algebraMap Aprime Bprime) (RingHom.ker qB) := sorry

/-- In a commutative square, the image of an element of the source kernel lies
in the target kernel. -/
theorem map_mem_ker_of_comp_eq_comp
    (hcomm : qB.comp g = f.comp qA) (z : RingHom.ker qA) :
    g z ∈ RingHom.ker qB := sorry

/-- Lemma 10.143.11 (05YT): consider a commutative diagram with surjective
horizontal maps whose kernels are square-zero.  If the induced map `A → B` is
etale and the target kernel is the base change of the source kernel, then
`Aprime → Bprime` is etale. -/
@[stacks 05YT]
theorem etale_of_surjective_of_ker_eq_map_of_square_zero
    (hcomm : qB.comp g = f.comp qA)
    (hEtale : f.Etale)
    (hSurjA : Function.Surjective qA)
    (hSurjB : Function.Surjective qB)
    (hSqA : (RingHom.ker qA) ^ 2 = ⊥)
    (hSqB : (RingHom.ker qB) ^ 2 = ⊥)
    (hBaseChange :
      letI : Algebra Aprime Bprime := g.toAlgebra
      let hker : RingHom.ker qA ≤
          Ideal.comap (algebraMap Aprime Bprime) (RingHom.ker qB) :=
        ker_le_comap_algebraMap_of_comp_eq_comp g qA qB f hcomm
      letI : Algebra (Aprime ⧸ RingHom.ker qA) (Bprime ⧸ RingHom.ker qB) :=
        Ideal.Quotient.algebraQuotientOfLEComap hker
      ∃ e :
          ((Bprime ⧸ RingHom.ker qB) ⊗[Aprime ⧸ RingHom.ker qA]
              (RingHom.ker qA).Cotangent) ≃ₗ[Bprime ⧸ RingHom.ker qB]
            (RingHom.ker qB).Cotangent,
        ∀ z : RingHom.ker qA,
          e (1 ⊗ₜ[Aprime ⧸ RingHom.ker qA]
              Ideal.toCotangent (RingHom.ker qA) z) =
            Ideal.toCotangent (RingHom.ker qB)
              ⟨g z, map_mem_ker_of_comp_eq_comp g qA qB f hcomm z⟩) :
    g.Etale := sorry

end

end RingHom

#check @RingHom.ker_le_comap_algebraMap_of_comp_eq_comp
#check @RingHom.map_mem_ker_of_comp_eq_comp
#check @RingHom.etale_of_surjective_of_ker_eq_map_of_square_zero

#print axioms RingHom.etale_of_surjective_of_ker_eq_map_of_square_zero
