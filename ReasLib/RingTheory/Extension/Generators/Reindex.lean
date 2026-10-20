module

public import Mathlib.RingTheory.Extension.Generators
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing algebra generators

This file owns the canonical presentation morphisms induced by an equivalence of generator
types.  It is independent of cotangent modules and homological complexes.
-/

@[expose] public section

noncomputable section

universe u v w x

namespace Algebra.Generators

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type w} {ι' : Type x}

/-- Renaming variables along `e` respects evaluation for the reindexed presentation. -/
theorem reindexTo_aeval (P : Generators R S ι') (e : ι ≃ ι') (i : ι) :
    MvPolynomial.aeval (R := R) P.val (MvPolynomial.X (e i)) =
      (P.reindex e).val i := sorry

/-- The canonical presentation morphism from `P.reindex e` to `P`. -/
@[stacks 00FQ "reindexing presentation morphism"]
noncomputable def reindexTo (P : Generators R S ι') (e : ι ≃ ι') :
    (P.reindex e).Hom P where
  val i := MvPolynomial.X (e i)
  aeval_val := reindexTo_aeval P e

/-- Renaming variables along `e.symm` respects evaluation in the reverse direction. -/
theorem reindexFrom_aeval (P : Generators R S ι') (e : ι ≃ ι') (i : ι') :
    MvPolynomial.aeval (R := R) (P.reindex e).val
      (MvPolynomial.X (e.symm i)) = P.val i := sorry

/-- The canonical presentation morphism from `P` to `P.reindex e`. -/
@[stacks 00FQ "inverse reindexing presentation morphism"]
noncomputable def reindexFrom (P : Generators R S ι') (e : ι ≃ ι') :
    P.Hom (P.reindex e) where
  val i := MvPolynomial.X (e.symm i)
  aeval_val := reindexFrom_aeval P e

end Algebra.Generators
