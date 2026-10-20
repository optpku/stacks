module

public import Mathlib.Algebra.MvPolynomial.Eval
public import ReasLib.RingTheory.RingHom.Fiber.Basic
public import ReasLib.RingTheory.RingHom.FiniteType.QuasiFinite

/-!
# Weak relative Noether normalization

A finite-type algebra whose fibers have uniformly bounded Krull dimension
admits a finite-type quasi-finite coordinate map from a polynomial algebra.
-/

@[expose] public section

universe u v

namespace RingHom.FibersKrullDimLE

/-- If every fiber of a finite-type algebra has Krull dimension at most `d`,
then the algebra admits a finite-type quasi-finite coordinate map from the
polynomial algebra in `d` variables. -/
@[stacks 0GTG "weak relative Noether normalization"]
theorem exists_quasiFinite_mvPolynomial
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (d : ℕ)
    (h : RingHom.FibersKrullDimLE d (algebraMap R S)) :
    ∃ f : MvPolynomial (Fin d) R →ₐ[R] S,
      RingHom.FiniteType.QuasiFinite f.toRingHom := sorry

end RingHom.FibersKrullDimLE
