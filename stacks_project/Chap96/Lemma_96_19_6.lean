module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.AbelianSheaf.Exactness
import StacksCheckRecall

/-!
# Exactness of abelian sheaves after inverse image along a covering 1-morphism

The source-facing statement is provided by the shared exactness owner.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u w

/- Lemma 96.19.6: source-facing bridge to the exactness reflection theorem. -/
@[stacks 06XD]
#check (AlgebraicGeometry.GroupoidsOver.exact_of_inverseImage_exact :
  ∀ {S : Scheme.{u}} {U X : GroupoidsOver S} (f : U ⟶ X) (τ : StandardTopology),
    [HasWeakSheafify (U.associatedTopology τ) AddCommGrpCat.{w}] →
    (C : ShortComplex (Sheaf (X.associatedTopology τ) AddCommGrpCat.{w})) →
    (hf : AlgebraicGeometry.GroupoidsOver.coversByEssentialImage f τ) →
    (hC : (C.map ((toFunctor f).sheafPullbackCocontinuous AddCommGrpCat.{w}
      (U.associatedTopology τ) (X.associatedTopology τ))).Exact) →
    C.Exact)
