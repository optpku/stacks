module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Coinvariants of a left group-ring module

This leaf owns the coinvariants `P_G` of a left `Λ[G]`-module as the quotient of `P` by the
`Λ`-span of `{g • p - p}`, together with the coequalizer/universal-property API recovering
the source identification `P_G = Λ ⊗_{Λ[G]} P` without using `TensorProduct`.
-/

@[expose] public section

noncomputable section

universe u v w x

open scoped MonoidAlgebra

namespace MonoidAlgebra

variable (Λ : Type u) (G : Type v) (P : Type w)
variable [Ring Λ] [Monoid G] [AddCommGroup P]
variable [Module (Λ[G]) P] [Module Λ P]

/-- The kernel of the coinvariants quotient: the `Λ`-span of `{g • p - p}` for the given
`Λ[G]`-action. -/
def Coinvariants.ker : Submodule Λ P :=
  Submodule.span Λ
    (Set.range fun gp : G × P ↦ (single gp.1 (1 : Λ) : Λ[G]) • gp.2 - gp.2)

/-- The coinvariants `P_G` of a left `Λ[G]`-module, as the quotient `P ⧸ ker`. -/
def Coinvariants : Type w :=
  P ⧸ Coinvariants.ker Λ G P

namespace Coinvariants

/-- The additive group structure on coinvariants, inherited from the quotient. -/
instance instAddCommGroup : AddCommGroup (Coinvariants Λ G P) :=
  inferInstanceAs (AddCommGroup (P ⧸ ker Λ G P))

/-- The left `Λ`-module structure on coinvariants, inherited from the quotient. -/
instance instModule : Module Λ (Coinvariants Λ G P) :=
  inferInstanceAs (Module Λ (P ⧸ ker Λ G P))

/-- Differences `g • p - p` lie in the coinvariants kernel. -/
theorem sub_mem_ker (g : G) (p : P) :
    (single g (1 : Λ) : Λ[G]) • p - p ∈ ker Λ G P :=
  sorry

/-- The canonical `Λ`-linear quotient map `P → P_G`. -/
def mk : P →ₗ[Λ] Coinvariants Λ G P :=
  Submodule.mkQ (ker Λ G P)

/-- The quotient map sends `p` to its class in the coinvariants. -/
theorem mk_apply (p : P) : mk Λ G P p = Submodule.Quotient.mk p :=
  sorry

/-- Equality of classes in the coinvariants is membership of the difference in `ker`. -/
theorem mk_eq_iff {p q : P} :
    mk Λ G P p = mk Λ G P q ↔ p - q ∈ ker Λ G P :=
  sorry

/-- The zero class is the kernel of the quotient map. -/
theorem mk_eq_zero {p : P} : mk Λ G P p = 0 ↔ p ∈ ker Λ G P :=
  sorry

/-- The quotient map to coinvariants is surjective. -/
theorem mk_surjective : Function.Surjective (mk Λ G P) :=
  sorry

/-- Group elements act trivially on classes in the coinvariants. -/
theorem mk_smul (g : G) (p : P) :
    mk Λ G P ((single g (1 : Λ) : Λ[G]) • p) = mk Λ G P p :=
  sorry

/-- Induction on a coinvariants class, reducing to a representative in `P`. -/
theorem induction_on {motive : Coinvariants Λ G P → Prop} (x : Coinvariants Λ G P)
    (h : ∀ p : P, motive (mk Λ G P p)) : motive x :=
  sorry

/-- A `G`-invariant `Λ`-linear map out of `P` descends to the coinvariants. -/
def lift {M : Type x} [AddCommGroup M] [Module Λ M] (f : P →ₗ[Λ] M)
    (hf : ∀ g : G, ∀ p : P, f ((single g (1 : Λ) : Λ[G]) • p) = f p) :
    Coinvariants Λ G P →ₗ[Λ] M :=
  Submodule.liftQ (ker Λ G P) f sorry

/-- Descent recovers the original map on representatives. -/
theorem lift_mk {M : Type x} [AddCommGroup M] [Module Λ M] (f : P →ₗ[Λ] M)
    (hf : ∀ g : G, ∀ p : P, f ((single g (1 : Λ) : Λ[G]) • p) = f p) (p : P) :
    lift Λ G P f hf (mk Λ G P p) = f p :=
  sorry

/-- Descent composed with the quotient map is the original `G`-invariant map. -/
theorem lift_comp_mk {M : Type x} [AddCommGroup M] [Module Λ M] (f : P →ₗ[Λ] M)
    (hf : ∀ g : G, ∀ p : P, f ((single g (1 : Λ) : Λ[G]) • p) = f p) :
    (lift Λ G P f hf).comp (mk Λ G P) = f :=
  sorry

/-- The coinvariants corepresent `G`-invariant `Λ`-linear maps out of `P`, recovering the
source coequalizer presentation of `P_G = Λ ⊗_{Λ[G]} P`. -/
theorem lift_spec {M : Type x} [AddCommGroup M] [Module Λ M] (f : P →ₗ[Λ] M)
    (hf : ∀ g : G, ∀ p : P, f ((single g (1 : Λ) : Λ[G]) • p) = f p) :
    f = (lift Λ G P f hf).comp (mk Λ G P) :=
  sorry

/-- Two maps out of the coinvariants agree if they agree on the image of `mk`. -/
theorem hom_ext {M : Type x} [AddCommGroup M] [Module Λ M]
    {f g : Coinvariants Λ G P →ₗ[Λ] M}
    (h : f.comp (mk Λ G P) = g.comp (mk Λ G P)) : f = g :=
  sorry

/-- Coinvariants of a finite left `Λ[G]`-module, for finite `G`, remain finite over `Λ`. -/
instance instFinite [Finite G] [IsScalarTower Λ (Λ[G]) P] [Module.Finite (Λ[G]) P] :
    Module.Finite Λ (Coinvariants Λ G P) :=
  sorry

/-- Coinvariants of a finite projective left `Λ[G]`-module, for finite `G`, remain
projective over `Λ`. -/
instance instProjective [Finite G] [IsScalarTower Λ (Λ[G]) P]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P] :
    Module.Projective Λ (Coinvariants Λ G P) :=
  sorry

end Coinvariants

end MonoidAlgebra
