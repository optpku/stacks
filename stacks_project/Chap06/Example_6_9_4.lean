/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Pointwise.Product
public import ReasLib.Topology.Sheaves.Pointwise.SectionwiseDiscrete
import StacksCheckRecall

@[expose] public section

open CategoryTheory
universe v

namespace Example_6_9_4

section

variable (A : ℕ → Type v)

/- The first three declarations expose the categorical mechanism behind the counterexample.
`TopCat.forget_preservesLimits` verifies the stronger limit-preservation property, while the
failure to reflect isomorphisms is deliberately stated separately because it is exactly the
hypothesis missing from `TopCat.Presheaf.isSheaf_iff_isSheaf_comp'`.
-/

/- Example 6.9.4 (1): the natural forgetful functor `TopCat ⥤ Type` is faithful. -/
@[stacks 0075 "the forgetful functor from topological spaces is faithful"]
#check (inferInstance : (forget TopCat.{v}).Faithful)

/- Example 6.9.4 (2): the forgetful functor `TopCat ⥤ Type` preserves products and equalizers;
in fact, mathlib proves that it preserves all limits. -/
@[stacks 0075 "the forgetful functor preserves products and equalizers"]
recall TopCat.forget_preservesLimits

/- Example 6.9.4 (3): the forgetful functor `TopCat ⥤ Type` does not reflect isomorphisms. -/
@[stacks 0075 "the forgetful functor does not reflect isomorphisms"]
recall TopCat.forget_not_reflectsIsomorphisms

/- The remaining clauses use the shared sectionwise-discrete and product-topology owners.  These
are distinct topological presheaves with the same dependent-function sections. -/

/- Example 6.9.4 (4): after every section space is given the discrete topology, forgetting the
topology recovers a sheaf of sets. -/
@[stacks 0075 "the sectionwise-discrete presheaf is a sheaf after forgetting topology"]
#check (TopCat.Presheaf.SectionwiseDiscrete.underlying_isSheaf
  (X := TopCat.of ℕ) A)

/- Example 6.9.4 (5): if every fibre has at least two elements, giving every section space the
discrete topology does not produce a sheaf of topological spaces. -/
@[stacks 0075 "the sectionwise-discrete presheaf is not a sheaf of topological spaces"]
#check fun [_hA : ∀ i : ℕ, Nontrivial (A i)] ↦
  TopCat.Presheaf.SectionwiseDiscrete.not_isSheaf_of_infinite_discrete
    (X := TopCat.of ℕ) A

/- Example 6.9.4 (6): giving the section space `∏ i : U, A i` its product topology does produce a
sheaf of topological spaces on the discrete space `ℕ`. -/
@[stacks 0075 "the product-topology presheaf is a sheaf of topological spaces"]
#check (TopCat.Presheaf.PointwiseProduct.isSheaf_topCat
  (fun i : TopCat.of ℕ ↦ (TopCat.discrete.obj (A i) : TopCat.{v})))
/- This is the specialization of the generic `TopCat` pointwise-product sheaf theorem to the
discrete topological space on `ℕ`. -/

end

end Example_6_9_4
