module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Big
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

/-!
# Small pro-étale base change on a chosen site

Base change sends a weakly étale object `U / S` in a chosen
big pro-étale presentation to the fibre product `U ×_S T / T` along a carrier
morphism `f : T ⟶ S`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X : ChosenBigProetaleSite.{u, v}} {S T : X.carrier}

/-- Pullback along a carrier morphism preserves the weakly étale object
property of the chosen small pro-étale site. -/
theorem smallObjects_map_pullback (f : T ⟶ S) (U : smallSite X S) :
    smallObjects X T ((smallInclusion X S ⋙ Big.pullback f).obj U) := sorry

/-- Base change along `f` on chosen small pro-étale sites. On objects it sends
`U / S` to `U ×_S T / T`. -/
def smallPullback (f : T ⟶ S) : smallSite X S ⥤ smallSite X T :=
  (smallObjects X T).lift (smallInclusion X S ⋙ Big.pullback f)
    (smallObjects_map_pullback f)

/-- The chosen small-site pullback sits over the chosen big-slice pullback via
the small-to-big inclusions. -/
def smallPullback_comp_smallInclusion (f : T ⟶ S) :
    smallPullback f ⋙ smallInclusion X T ≅ smallInclusion X S ⋙ Big.pullback f :=
  (smallObjects X T).liftCompιIso (smallInclusion X S ⋙ Big.pullback f)
    (smallObjects_map_pullback f)

/-- Base change along `f` preserves the terminal object of the chosen small
pro-étale site, sending `S / S` to a terminal object over `T`. -/
theorem smallPullback_preservesTerminal (f : T ⟶ S) :
    PreservesLimit (Functor.empty.{0} (smallSite X S)) (smallPullback f) :=
  sorry

/-- Chosen small pro-étale base change is continuous. -/
theorem smallPullback_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (smallPullback f) (smallTopology X S)
      (smallTopology X T) := sorry

/-- Chosen small pro-étale base change preserves fibre products. -/
theorem smallPullback_preservesPullbacks (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (smallPullback f) := sorry

/-- Chosen small pro-étale base change is a morphism of sites. -/
theorem smallPullback_isMorphismOfSites (f : T ⟶ S) :
    IsMorphismOfSites (smallTopology X S) (smallTopology X T)
      (smallPullback f) := sorry

/-- The opposite small-site pullback has the left Kan extensions used by sheaf
pullback. -/
theorem smallPullback_op_hasLeftKanExtension
    (f : T ⟶ S) [UnivLE.{max u v, w}] (P : (smallSite X S)ᵒᵖ ⥤ Type w) :
    (smallPullback f).op.HasLeftKanExtension P := sorry

/-- Sheaf pullback along chosen small pro-étale base change preserves finite
limits. -/
theorem smallPullback_sheafPullback_preservesFiniteLimits (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasWeakSheafify (smallTopology X T) (Type w)] :
    PreservesFiniteLimits
      (@Functor.sheafPullback _ _ _ _ (smallPullback f) (Type w) _
        (smallTopology X S) (smallTopology X T) (smallPullback_isContinuous f)
        (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
          (smallPullback f) (Type w) _ (smallTopology X S) (smallTopology X T)
          (smallPullback_isContinuous f) (smallPullback_op_hasLeftKanExtension f)
          inferInstance).isRightAdjoint) := sorry

end AlgebraicGeometry.ChosenBigProetaleSite
