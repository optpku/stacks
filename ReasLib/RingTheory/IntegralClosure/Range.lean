module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integral Closure and Ring-Hom Ranges

@stack 00PX
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The range of a ring homomorphism is integrally closed in the target exactly when the integral
closure for the induced algebra structure is bottom. -/
@[stacks 00PX "integrally closed range criterion"]
theorem isIntegrallyClosedIn_range_iff (f : R →+* S) :
    IsIntegrallyClosedIn f.range S ↔
      (letI : Algebra R S := f.toAlgebra
       integralClosure R S = ⊥) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R f.range := f.rangeRestrict.toAlgebra
  letI : IsScalarTower R f.range S := .of_algebraMap_eq fun _ ↦ rfl
  constructor
  · intro h
    apply le_antisymm
    · intro x hx
      rw [Algebra.mem_bot]
      have hx' : _root_.IsIntegral f.range x :=
        (show _root_.IsIntegral R x from hx).tower_top
      have hx'' : x ∈ f.range := (Subring.isIntegrallyClosedIn_iff.mp h) hx'
      simpa [RingHom.algebraMap_toAlgebra] using hx''
    · exact bot_le
  · intro h
    letI : Algebra.IsIntegral R f.range :=
      ⟨f.rangeRestrict.isIntegral_of_surjective f.rangeRestrict_surjective⟩
    rw [Subring.isIntegrallyClosedIn_iff]
    intro x hx
    have hxR : _root_.IsIntegral R x := isIntegral_trans (R := R) x hx
    have hxbot : x ∈ (⊥ : Subalgebra R S) := h ▸ hxR
    rw [Algebra.mem_bot] at hxbot
    simpa [RingHom.algebraMap_toAlgebra] using hxbot

end RingHom
