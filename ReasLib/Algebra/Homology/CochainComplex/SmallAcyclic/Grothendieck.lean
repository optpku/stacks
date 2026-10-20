module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import ReasLib.Algebra.Homology.CochainComplex.SmallAcyclic.Termwise
public import ReasLib.CategoryTheory.Generator.CoproductCardinal

@[expose] public section

/-!
# Small Acyclic Complexes in Grothendieck Abelian Categories

Grothendieck abelian categories admit one cardinal controlling both nonzero small acyclic
subcomplexes and coproduct presentations of arbitrary acyclic complexes.
-/

open CategoryTheory

universe w v u

namespace CochainComplex.SmallAcyclic

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- Lemma 19.12.2: one cardinal uniformly controls nonzero small acyclic subcomplexes and
coproduct presentations of acyclic cochain complexes in a Grothendieck abelian category. The
chosen bound lives in a successor universe; the predicates it satisfies accept bounds in any
universe. -/
@[stacks 079K "uniform cardinal"]
theorem exists_bound :
    ∃ kappa : Cardinal.{max u v + 1},
      IsUniformBound C kappa := sorry

/-- The uniform small-acyclic-subcomplex consequence of `exists_bound`. -/
theorem exists_subcomplex_bound :
    ∃ kappa : Cardinal.{max u v + 1}, HasSubcomplexes C kappa := sorry

/-- The uniform acyclic coproduct-presentation consequence of `exists_bound`. -/
theorem exists_coproduct_presentation_bound :
    ∃ kappa : Cardinal.{max u v + 1}, HasCoproductPresentations C kappa := sorry

end CochainComplex.SmallAcyclic
