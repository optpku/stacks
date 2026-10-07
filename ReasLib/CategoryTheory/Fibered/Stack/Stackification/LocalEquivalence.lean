module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
import Mathlib.Tactic.CrossRefAttribute

/-!
# The local-equivalence projection of a stackification

The heterogeneous projection is a field of the canonical `CartesianBasedFunctor.IsStackification`
owner. This leaf supplies only the fixed-universe specialization used by bicategorical consumers.
-/

@[expose] public section

universe u v w vS uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Hom.IsStackification

variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- The fixed-universe specialization of the heterogeneous theorem that a stackification is a
local equivalence. -/
@[stacks 02ZN "fixed-universe stackification is a local equivalence"]
theorem isLocalEquivalence
    {J : GrothendieckTopology C} {F : X ⟶ Y}
    (hF : IsStackification J F) :
    IsLocalEquivalence J F := sorry

end FiberedCategoryOver.Hom.IsStackification

end CategoryTheory
