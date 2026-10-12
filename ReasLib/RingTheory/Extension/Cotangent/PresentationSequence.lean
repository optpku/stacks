/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.Exact.Prod

/-!
# Conormal sequences for algebra presentations

@stack 07EW
@stack 07EX

This leaf records reusable exact sequences obtained from composable algebra
presentations. It also provides the stable form obtained by adding the same
free summand to the first two terms.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace Algebra.Generators.Cotangent

variable {R : Type u} {A : Type v} {C : Type w}
variable [CommRing R] [CommRing A] [CommRing C]
variable [Algebra R A] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
variable {ι : Type x} {m : ℕ}

/-- For composable presentations, postcomposing the canonical conormal map
with a linear equivalence preserves exactness and surjectivity. -/
@[stacks 07EW]
theorem exact_postcomp_equiv
    (P : Algebra.Generators R A ι)
    (Q : Algebra.Generators A C (Fin m))
    (q : Q.toExtension.CotangentSpace →ₗ[A] P.toExtension.Cotangent)
    (e : Q.toExtension.Cotangent ≃ₗ[C] C ⊗[A] LinearMap.ker q) :
    Function.Exact
        ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange C)
        (e.toLinearMap ∘ₗ Extension.Cotangent.map (Q.ofComp P).toExtensionHom) ∧
      Function.Surjective
        (e.toLinearMap ∘ₗ Extension.Cotangent.map (Q.ofComp P).toExtensionHom) := sorry

/-- 16.3.1.2: adding the same module as a direct summand to the first two terms
of the presentation conormal sequence preserves exactness and right
surjectivity. -/
@[stacks 07EX]
theorem exact_stabilized_postcomp_equiv
    {F : Type*} [AddCommMonoid F] [Module C F]
    (P : Algebra.Generators R A ι)
    (Q : Algebra.Generators A C (Fin m))
    (q : Q.toExtension.CotangentSpace →ₗ[A] P.toExtension.Cotangent)
    (e : Q.toExtension.Cotangent ≃ₗ[C] C ⊗[A] LinearMap.ker q) :
    Function.Exact
        ((LinearMap.id : F →ₗ[C] F).prodMap
          ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange C))
        ((e.toLinearMap ∘ₗ Extension.Cotangent.map (Q.ofComp P).toExtensionHom) ∘ₗ
          LinearMap.snd C F (Q.comp P).toExtension.Cotangent) ∧
      Function.Surjective
        ((e.toLinearMap ∘ₗ Extension.Cotangent.map (Q.ofComp P).toExtensionHom) ∘ₗ
          LinearMap.snd C F (Q.comp P).toExtension.Cotangent) := sorry

end Algebra.Generators.Cotangent
