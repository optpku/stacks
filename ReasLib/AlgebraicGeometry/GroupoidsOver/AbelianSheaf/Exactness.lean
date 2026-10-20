module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Covering
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.Zero
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exactness reflection for abelian sheaves

A complex of abelian sheaves on a groupoid-fibred site is exact when its
cocontinuous inverse image is exact and the underlying morphism covers by
essential image.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S} (f : U ⟶ X) (τ : StandardTopology)

/-- Exactness of a complex of abelian sheaves descends along a morphism whose
underlying functor is cover dense on the associated site. -/
@[stacks 06XD]
theorem exact_of_inverseImage_exact
    [HasWeakSheafify (U.associatedTopology τ) AddCommGrpCat.{w}]
    (C : ShortComplex (Sheaf (X.associatedTopology τ) AddCommGrpCat.{w}))
    (hf : coversByEssentialImage f τ)
    (hC : (C.map ((toFunctor f).sheafPullbackCocontinuous AddCommGrpCat.{w}
            (U.associatedTopology τ) (X.associatedTopology τ))).Exact) :
    C.Exact :=
  sorry

end AlgebraicGeometry.GroupoidsOver
