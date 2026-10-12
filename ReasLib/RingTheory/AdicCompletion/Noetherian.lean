/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Noetherian adic completions

The general owner is the local criterion `IsAdicComplete.isNoetherianRing`: completeness along a
finitely generated ideal and Noetherianity of the quotient imply Noetherianity of the ring.  The
adic-completion declarations specialize this criterion and expose the canonical quotient
comparison and typeclass instance used by downstream completion arguments.
-/

@[expose] public section

universe u

namespace IsAdicComplete

/-- A ring complete along a finitely generated ideal is Noetherian when the quotient by that
ideal is Noetherian. Completeness is an explicit proof so callers need not install a temporary
instance. -/
@[stacks 05GH "complete criterion"]
theorem isNoetherianRing {R : Type u} [CommRing R] {I : Ideal R}
    (h_complete : IsAdicComplete I R) [IsNoetherianRing (R ⧸ I)] (hI : I.FG) :
    IsNoetherianRing R := sorry

end IsAdicComplete

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- The quotient of an adic completion by the extended defining ideal is canonically the
original quotient, as an `R`-algebra. -/
@[stacks 05GH "quotient comparison"]
noncomputable def quotientExtensionEquiv (I : Ideal R) (hI : I.FG) :
    (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R))) ≃ₐ[R] R ⧸ I :=
  (Ideal.quotientEquivAlgOfEq R (AdicCompletion.ker_evalOneₐ_eq_map I hI).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := AdicCompletion.evalOneₐ I) (AdicCompletion.evalOneₐ_surjective I))

/-- The quotient comparison evaluates a completion class through the first-stage map. -/
@[simp, stacks 05GH "quotient comparison apply"]
theorem quotientExtensionEquiv_mk (I : Ideal R) (hI : I.FG) (x : AdicCompletion I R) :
    quotientExtensionEquiv I hI
        (Ideal.Quotient.mk (I.map (algebraMap R (AdicCompletion I R))) x) =
      AdicCompletion.evalOneₐ I x := sorry

/-- If `R ⧸ I` is Noetherian, then so is the quotient of the `I`-adic completion by the
extended ideal. -/
@[stacks 05GH "Noetherian quotient"]
theorem quotientExtension_isNoetherianRing (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] :
    IsNoetherianRing
      (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R))) := sorry

/-- The `I`-adic completion of a commutative ring is Noetherian when `I` is finitely generated
and the quotient `R ⧸ I` is Noetherian. -/
@[stacks 05GH "(1)"]
theorem isNoetherianRing (I : Ideal R) (hI : I.FG) [IsNoetherianRing (R ⧸ I)] :
    IsNoetherianRing (AdicCompletion I R) := sorry

/-- The adic completion of a Noetherian commutative ring along any ideal is Noetherian. -/
@[stacks 0316, instance]
instance instIsNoetherianRing (I : Ideal R) [IsNoetherianRing R] :
    IsNoetherianRing (AdicCompletion I R) := sorry

end AdicCompletion

variable {R : Type u} [CommRing R]

/-- The adic completion is Noetherian and complete along its extended defining ideal when the
quotient by that ideal is Noetherian and the ideal is finitely generated. -/
theorem adicCompletion_isNoetherian_and_isAdicComplete (I : Ideal R)
    [IsNoetherianRing (R ⧸ I)] (hI : I.FG) :
    IsNoetherianRing (AdicCompletion I R) ∧
      IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) := sorry

/-- The adic completion of a Noetherian commutative ring along any ideal is Noetherian. -/
theorem adicCompletion_isNoetherianRing [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R) := sorry
