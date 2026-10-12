/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Definition_61_12_8_Presentation
public import stacks_project.Chap61.Lemma_61_12_10_Limits
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Nested small pro-étale inclusions

This leaf owns the inclusion of nested chosen small pro-étale sites induced by
a fully faithful carrier functor of two chosen big-site presentations, together
with the Sites 7.21.8 instances on that inclusion.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite

/-- The chosen small pro-étale site of an object has fibre products. -/
instance smallSite_hasPullbacks (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) :
    HasPullbacks (smallSite X S) :=
  smallSiteHasPullbacks X S

variable {X Y : ChosenBigProetaleSite.{u, v}}

/-- Carrier postcomposition along a scheme-compatible functor preserves the
weakly étale object property of a chosen small pro-étale site. -/
theorem smallObjects_map_post (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme) (U : smallSite X S) :
    smallObjects Y (ι.obj S) ((smallInclusion X S ⋙ Over.post ι).obj U) := sorry

/-- The inclusion of nested chosen small pro-étale sites induced by a
scheme-compatible carrier functor. On objects it sends `U / S` in the smaller
presentation to the same structural morphism viewed in the larger
presentation. -/
def smallNestedInclusion (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    smallSite X S ⥤ smallSite Y (ι.obj S) :=
  (smallObjects Y (ι.obj S)).lift (smallInclusion X S ⋙ Over.post ι)
    (smallObjects_map_post S ι e)

/-- The nested small inclusion sits over carrier postcomposition via the
small-to-big inclusion of the larger presentation. -/
theorem smallNestedInclusion_obj (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme) (U : smallSite X S) :
    (smallInclusion Y (ι.obj S)).obj ((smallNestedInclusion S ι e).obj U) =
      (Over.post ι).obj U.obj := sorry

/-- The nested small inclusion triangle is the identity after including into
the larger chosen big slice. -/
def smallNestedInclusion_comp_smallInclusion (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    smallNestedInclusion S ι e ⋙ smallInclusion Y (ι.obj S) ≅
      smallInclusion X S ⋙ Over.post ι :=
  (smallObjects Y (ι.obj S)).liftCompιIso (smallInclusion X S ⋙ Over.post ι)
    (smallObjects_map_post S ι e)

/-- The nested small-inclusion triangle isomorphism is the identity on
objects of the larger chosen big slice. -/
theorem smallNestedInclusion_comp_smallInclusion_hom_app (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    (U : smallSite X S) :
    (smallNestedInclusion_comp_smallInclusion S ι e).hom.app U =
      𝟙 ((smallNestedInclusion S ι e ⋙ smallInclusion Y (ι.obj S)).obj U) := sorry

/-- The nested small inclusion sends `S / S` to the identity object of the
larger small site. -/
def smallNestedInclusion_obj_smallTerminalObject_iso (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    (smallNestedInclusion S ι e).obj (smallTerminalObject X S) ≅
      smallTerminalObject Y (ι.obj S) :=
  (smallObjects Y (ι.obj S)).isoMk (eqToIso (congrArg Over.mk (ι.map_id S)))

/-- The identity-object identification for the nested small inclusion is the
identity on the underlying source scheme of the larger presentation. -/
theorem smallNestedInclusion_obj_smallTerminalObject_iso_hom_left (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    ((smallInclusion Y (ι.obj S)).map
        (smallNestedInclusion_obj_smallTerminalObject_iso S ι e).hom).left =
      𝟙 (ι.obj S) := sorry

/-- The nested small inclusion sends the final object `S / S` of the smaller
site to a final object of the larger small site. -/
def smallNestedInclusion_obj_smallTerminalObject (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    IsTerminal ((smallNestedInclusion S ι e).obj (smallTerminalObject X S)) :=
  (smallTerminalObjectIsTerminal Y (ι.obj S)).ofIso
    (smallNestedInclusion_obj_smallTerminalObject_iso S ι e).symm

/-- The nested small inclusion is full when the carrier functor is fully
faithful. -/
instance smallNestedInclusion_full (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme) [ι.Full] [ι.Faithful] :
    (smallNestedInclusion S ι e).Full := sorry

/-- The nested small inclusion is faithful when the carrier functor is
faithful. -/
instance smallNestedInclusion_faithful (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme) [ι.Faithful] :
    (smallNestedInclusion S ι e).Faithful := sorry

/-- The nested small inclusion is continuous for the chosen small pro-étale
topologies, using covering containment of the carrier functor on the chosen
big-site topologies. -/
instance smallNestedInclusion_isContinuous (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [ι.IsContinuous X.toGrothendieck Y.toGrothendieck] :
    (smallNestedInclusion S ι e).IsContinuous (smallTopology X S)
      (smallTopology Y (ι.obj S)) := sorry

/-- The nested small inclusion is cocontinuous for the chosen small pro-étale
topologies. -/
instance smallNestedInclusion_isCocontinuous (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    (smallNestedInclusion S ι e).IsCocontinuous (smallTopology X S)
      (smallTopology Y (ι.obj S)) := sorry

/-- The nested small inclusion preserves fibre products. -/
instance smallNestedInclusion_preservesPullbacks (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    PreservesLimitsOfShape WalkingCospan (smallNestedInclusion S ι e) := sorry

/-- Sheaf pullback along the nested small inclusion preserves finite limits,
once left Kan extensions of `Type w`-valued presheaves exist. -/
instance smallNestedInclusion_sheafPullback_preservesFiniteLimits (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [ι.IsContinuous X.toGrothendieck Y.toGrothendieck]
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ Type w,
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((smallNestedInclusion S ι e).sheafPullback (Type w)
        (smallTopology X S) (smallTopology Y (ι.obj S))) := sorry

end AlgebraicGeometry.ChosenBigProetaleSite
