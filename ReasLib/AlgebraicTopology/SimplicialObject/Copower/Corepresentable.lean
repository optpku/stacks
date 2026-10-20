module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower
public import ReasLib.CategoryTheory.Functor.IndexedCoproduct.HomFamily
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatible families for simplicial copowers

The universal property of maps out of a simplicial copower is the `SimplexCategory`
specialization of the category-generic indexed-coproduct Hom-family API. This file records that
specialization without introducing a second owner or compatibility aliases.

@stack 017B
@stack 017D
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (U : SSet.{w}) (V W : SimplicialObject C)
variable [SimplicialObject.HasCopower U V]

/- Lemma 14.13.2 (017D): compatible simplex-indexed families are corepresented by the
simplicial copower. The owner is generic in the indexing category. -/

/- The source compatibility equation is the generic presheaf compatibility condition. -/

/- The underlying Hom equivalence is available independently of its corepresentability
packaging. -/

end CategoryTheory
