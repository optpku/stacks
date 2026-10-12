/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap10.Example_10_119_5.KrullAkizukiBridge
import StacksCheckRecall

/-!
Linear-independence and Laurent-dimension bridges used by Example 10.119.5.

@stack 00PB
-/

@[expose] public section

noncomputable section

universe u

open PowerSeries IsLocalRing
open AdicCompletion
open scoped Pointwise

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

open scoped PthPowerSubfield

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: finite coefficient-field extensions preserve the
infinite-dimensionality of `k` after changing scalars from `k^p` to the finite intermediate
field. -/
lemma not_finiteDimensional_over_finitePthPowerIntermediate_of_base
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ FiniteDimensional L k := sorry

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: constants that are linearly independent over a fixed
intermediate coefficient field remain independent over the corresponding Laurent-series
subfield. -/
lemma linearIndependent_constLaurentSeries_of_linearIndependent
    (L : IntermediateField (k^[p]) k) {v : ℕ → k}
    (hv : LinearIndependent L v) :
    LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L)
      (fun i : ℕ ↦ (HahnSeries.C (v i) : LaurentSeries k)) := sorry

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: for each fixed finite coefficient field, there is a
countable Laurent-series family linearly independent over its Laurent-series subfield. -/
lemma exists_constLaurentSeries_linearIndependent_over_finiteCoeffLaurentSubfield
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ∃ v : ℕ → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v := sorry

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: restricting a countable independent family to an
initial finite segment preserves linear independence. -/
lemma linearIndependent_natRestrict_fin
    {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
    {v : ℕ → E} (hv : LinearIndependent F v) (r : ℕ) :
    LinearIndependent F (fun i : Fin r ↦ v i.1) := sorry

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: a countable independent family over the Laurent
coefficient union supplies independent finite initial segments of every size. -/
lemma exists_fin_linearIndependent_of_nat_finiteCoeffLaurentUnion
    (h :
      ∃ v : ℕ → LaurentSeries k,
        LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v)
    (r : ℕ) :
    ∃ v : Fin r → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := sorry

/-- Helper for Chap10 Example 10 119 5: arbitrarily large finite independent families rule out
finite-dimensionality of a vector space. -/
lemma not_finiteDimensional_of_forall_fin_linearIndependent
    {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
    (h : ∀ r : ℕ, ∃ v : Fin r → E, LinearIndependent F v) :
    ¬ FiniteDimensional F E := sorry

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: over any finite intermediate coefficient field,
infinite degree over `k^p` supplies coefficient blocks of every finite size. -/
lemma exists_coeffBlockLinearIndependent_over_finitePthPowerIntermediate
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (r : ℕ) :
    ∃ b : Fin r → k, LinearIndependent L b := sorry

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: over each fixed finite coefficient Laurent subfield,
there are independent Laurent families of every finite size. -/
lemma exists_constLaurentSeries_fin_linearIndependent_over_finiteCoeffLaurentSubfield
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (r : ℕ) :
    ∃ v : Fin r → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v := sorry

/-- Helper for Chap10 Example 10 119 5: Laurent series are not finite-dimensional over the
directed union of finite coefficient Laurent subfields. -/
@[stacks 00PB "Laurent dimension obstruction"]
lemma not_finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ FiniteDimensional (finiteCoeffLaurentUnion (k := k) (p := p)) (LaurentSeries k) := sorry

/-- Helper for Chap10 Example 10 119 5: infinite coefficient-field degree provides a countable
Laurent family over the directed finite-coefficient union. -/
lemma exists_nat_linearIndependent_over_finiteCoeffLaurentUnion_direct
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ∃ v : ℕ → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := sorry

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: a finite Laurent family that is independent over every
finite coefficient Laurent subfield is independent over the directed union. -/
lemma linearIndependent_fin_finiteCoeffLaurentUnion_of_uniform_finiteCoeffLaurentSubfield
    {r : ℕ} (v : Fin r → LaurentSeries k)
    (hv : ∀ (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L],
      LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v) :
    LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := sorry

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: linear independence over the directed union restricts
to every finite coefficient Laurent subfield. -/
lemma linearIndependent_finiteCoeffLaurentSubfield_of_finiteCoeffLaurentUnion
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    {ι : Type*} {v : ι → LaurentSeries k}
    (hv : LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v) :
    LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v := sorry

/-- Helper for Chap10 Example 10 119 5: infinite coefficient-field degree supplies finite
families of any prescribed size that are linearly independent over the finite-coefficient Laurent
union. -/
lemma exists_fin_linearIndependent_over_finiteCoeffLaurentUnion_direct
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (r : ℕ) :
    ∃ v : Fin r → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := sorry

end

@[stacks 00PB "finite intermediate-field obstruction"]
#check @not_finiteDimensional_over_finitePthPowerIntermediate_of_base

@[stacks 00PB "constant Laurent-series independence"]
#check @linearIndependent_constLaurentSeries_of_linearIndependent

@[stacks 00PB "Laurent dimension obstruction"]
#check @not_finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion

@[stacks 00PB "independence over the directed union"]
#check @linearIndependent_fin_finiteCoeffLaurentUnion_of_uniform_finiteCoeffLaurentSubfield

@[stacks 00PB "restriction to a finite coefficient field"]
#check @linearIndependent_finiteCoeffLaurentSubfield_of_finiteCoeffLaurentUnion
