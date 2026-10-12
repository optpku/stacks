/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap96.Lemma_96_19_6_Covering

/-!
# Exactness of abelian sheaves after inverse image along a covering 1-morphism

If a complex of abelian sheaves on `𝒳_τ` becomes exact after inverse image
along a 1-morphism that covers by essential image, then the original complex
is exact.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S} (f : U ⟶ X) (τ : StandardTopology)

/-- Lemma 96.19.6: Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. Let `τ` be a standard topology, and let `C` be
a complex in `Ab(𝒳_τ)`. If every object of `𝒳` admits a covering in `𝒳_τ` by
objects isomorphic to images under `f`, and the inverse image of `C` along `f`
is exact, then `C` is exact. -/
@[stacks 06XD]
theorem exact_of_inverseImage_exact
    [HasWeakSheafify (U.associatedTopology τ) AddCommGrpCat.{w}]
    [((toFunctor f).sheafPullbackCocontinuous AddCommGrpCat.{w}
        (U.associatedTopology τ) (X.associatedTopology τ)).PreservesZeroMorphisms]
    (C : ShortComplex (Sheaf (X.associatedTopology τ) AddCommGrpCat.{w}))
    (hf : coversByEssentialImage f τ)
    (hC : (C.map ((toFunctor f).sheafPullbackCocontinuous AddCommGrpCat.{w}
            (U.associatedTopology τ) (X.associatedTopology τ))).Exact) :
    C.Exact :=
  sorry

end AlgebraicGeometry.GroupoidsOver
