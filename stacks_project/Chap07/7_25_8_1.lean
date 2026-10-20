module

public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe uC vC w

namespace CategoryTheory.Over.Site

variable {C : Type uC} [Category.{vC} C]

variable (J : GrothendieckTopology C) {U V : C} (f : V ⟶ U)
    [HasSheafify (J.over U) (Type w)] [HasSheafify (J.over V) (Type w)]
    [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.forget V).op.HasPointwiseRightKanExtension P]

/- 7.25.8.1: for a site `(C, J)` and `f : V ⟶ U`, the morphisms of topoi induced by
`Over.map f : Over V ⥤ Over U`, `Over.forget U`, and `Over.forget V` form a commutative
triangle `Sh(Over V) ⟶ Sh(Over U)` over `Sh(C)`: the pushforward of `j_U` composed with `j`
is canonically isomorphic to the pushforward of `j_V`. -/
@[stacks 04IK] #check
  (CategoryTheory.Functor.sheafPushforwardCocontinuousComp'
    (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f) :
    (MorphismOfTopoiIn.comp
        ((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J)
        ((Over.map f).morphismOfTopoiInOfCocontinuous (J.over V) (J.over U))).pushforward ≅
      ((Over.forget V).morphismOfTopoiInOfCocontinuous (J.over V) J).pushforward)

/- Inverse-image mate of the pushforward comparison: `j_V⁻¹` is uniquely isomorphic to
`j_U⁻¹ ⋙ j⁻¹` as the left adjoint of the composite pushforward. -/
#check
  (CategoryTheory.Adjunction.leftAdjointUniq
    ((MorphismOfTopoiIn.comp
        ((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J)
        ((Over.map f).morphismOfTopoiInOfCocontinuous (J.over V) (J.over U))).adjunction.ofNatIsoRight
      (CategoryTheory.Functor.sheafPushforwardCocontinuousComp'
        (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f)))
    ((Over.forget V).morphismOfTopoiInOfCocontinuous (J.over V) J).adjunction :
    (MorphismOfTopoiIn.comp
        ((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J)
        ((Over.map f).morphismOfTopoiInOfCocontinuous (J.over V) (J.over U))).inverseImage ≅
      ((Over.forget V).morphismOfTopoiInOfCocontinuous (J.over V) J).inverseImage)

end CategoryTheory.Over.Site
