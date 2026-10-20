module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Variance
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Target maps on internal-hom pullbacks

For a fixed span of simplicial sets, postcomposition in the target induces the canonical map
between the corresponding objectwise pullbacks.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject.internalHom.pushout.pullback

variable {C : Type uC} [Category.{vC} C]
variable {U V W : SSet.{uS}} (a : U ⟶ V) (b : U ⟶ W)
variable [HasCopowers U C] [HasCopowers V C] [HasCopowers W C]

section Map

variable {T T' : SimplicialObject C} (p : T ⟶ T')
variable [HasInternalHom U T] [HasInternalHom V T] [HasInternalHom W T]
variable [HasInternalHom U T'] [HasInternalHom V T'] [HasInternalHom W T']
variable [HasPullback (precomp a T) (precomp b T)]
variable [HasPullback (precomp a T') (precomp b T')]

/-- The map between the pullbacks of a fixed simplicial-set span induced by
postcomposition in the target. -/
@[stacks 017N "target map on the internal-hom pullback of a span"]
def map :
    CategoryTheory.Limits.pullback (precomp a T) (precomp b T) ⟶
      CategoryTheory.Limits.pullback (precomp a T') (precomp b T') :=
  CategoryTheory.Limits.pullback.map (precomp a T) (precomp b T)
    (precomp a T') (precomp b T') (postcomp V p) (postcomp W p)
    (postcomp U p) (interchange a p) (interchange b p)

/-- The first projection of the target map on internal-hom pullbacks is
postcomposition on the left endpoint of the span. -/
@[reassoc (attr := simp), stacks 017N "first projection of the target pullback map"]
theorem map.fst :
    map a b p ≫
        CategoryTheory.Limits.pullback.fst (precomp a T') (precomp b T') =
      CategoryTheory.Limits.pullback.fst (precomp a T) (precomp b T) ≫
        postcomp V p := sorry

/-- The second projection of the target map on internal-hom pullbacks is
postcomposition on the right endpoint of the span. -/
@[reassoc (attr := simp), stacks 017N "second projection of the target pullback map"]
theorem map.snd :
    map a b p ≫
        CategoryTheory.Limits.pullback.snd (precomp a T') (precomp b T') =
      CategoryTheory.Limits.pullback.snd (precomp a T) (precomp b T) ≫
        postcomp W p := sorry

end Map

section Identity

variable (X : SimplicialObject C)
variable [HasInternalHom U X] [HasInternalHom V X] [HasInternalHom W X]
variable [HasPullback (precomp a X) (precomp b X)]

/-- The target map on internal-hom pullbacks preserves identity morphisms. -/
@[simp, stacks 017N "identity for the target pullback map"]
theorem map.id :
    map a b (𝟙 X) =
      𝟙 (CategoryTheory.Limits.pullback (precomp a X) (precomp b X)) := sorry

end Identity

section Composition

variable {X Y Z : SimplicialObject C} (p : X ⟶ Y) (q : Y ⟶ Z)
variable [HasInternalHom U X] [HasInternalHom V X] [HasInternalHom W X]
variable [HasInternalHom U Y] [HasInternalHom V Y] [HasInternalHom W Y]
variable [HasInternalHom U Z] [HasInternalHom V Z] [HasInternalHom W Z]
variable [HasPullback (precomp a X) (precomp b X)]
variable [HasPullback (precomp a Y) (precomp b Y)]
variable [HasPullback (precomp a Z) (precomp b Z)]

/-- The target map on internal-hom pullbacks preserves composition. -/
@[simp, stacks 017N "composition for the target pullback map"]
theorem map.comp : map a b (p ≫ q) = map a b p ≫ map a b q := sorry

end Composition

end CategoryTheory.SimplicialObject.internalHom.pushout.pullback
