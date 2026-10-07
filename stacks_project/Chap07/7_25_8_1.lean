module

public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

universe uC vC w

namespace CategoryTheory.Over.Site

variable {C : Type uC} [Category.{vC} C]

/-- 7.25.8.1: for a site `(C, J)` and `f : V ⟶ U`, the morphisms of topoi induced by
`Over.map f : Over V ⥤ Over U`, `Over.forget U`, and `Over.forget V` form a commutative
triangle `Sh(Over V) ⟶ Sh(Over U)` over `Sh(C)`: the pushforward of `j_U` composed with `j`
is canonically isomorphic to the pushforward of `j_V`. -/
@[stacks 04IK]
noncomputable def relocalizePushforwardIso (J : GrothendieckTopology C) {U V : C} (f : V ⟶ U)
    [HasSheafify (J.over U) (Type w)] [HasSheafify (J.over V) (Type w)]
    [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.forget V).op.HasPointwiseRightKanExtension P] :
    (MorphismOfTopoiIn.comp
        ((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J)
        ((Over.map f).morphismOfTopoiInOfCocontinuous (J.over V) (J.over U))).pushforward ≅
      ((Over.forget V).morphismOfTopoiInOfCocontinuous (J.over V) J).pushforward :=
  Functor.sheafPushforwardCocontinuousComp'
    (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f)

/-- Inverse-image mate of `relocalizePushforwardIso`: `j_V⁻¹` is uniquely isomorphic to
`j_U⁻¹ ⋙ j⁻¹` as the left adjoint of the composite pushforward. -/
noncomputable def relocalizeInverseImageIso (J : GrothendieckTopology C) {U V : C} (f : V ⟶ U)
    [HasSheafify (J.over U) (Type w)] [HasSheafify (J.over V) (Type w)]
    [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.forget V).op.HasPointwiseRightKanExtension P] :
    (MorphismOfTopoiIn.comp
        ((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J)
        ((Over.map f).morphismOfTopoiInOfCocontinuous (J.over V) (J.over U))).inverseImage ≅
      ((Over.forget V).morphismOfTopoiInOfCocontinuous (J.over V) J).inverseImage :=
  let localizationU := (Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J
  let relocalization := (Over.map f).morphismOfTopoiInOfCocontinuous (J.over V) (J.over U)
  let localizationV := (Over.forget V).morphismOfTopoiInOfCocontinuous (J.over V) J
  Adjunction.leftAdjointUniq
    ((MorphismOfTopoiIn.comp localizationU relocalization).adjunction.ofNatIsoRight
      (relocalizePushforwardIso J f))
    localizationV.adjunction

end CategoryTheory.Over.Site

