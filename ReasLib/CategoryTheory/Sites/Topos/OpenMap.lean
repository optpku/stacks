module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Presheaf
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint

/-!
# Sheaf direct images of open maps

The direct image induced by the cocontinuous functor on opens of an open map
agrees with the usual sheaf direct image.  This is an ambient topological API,
not a Chapter 7-specific comparison.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe w

namespace IsOpenMap

variable {X Y : TopCat.{w}} {f : X ⟶ Y}

/-- An open map induces a cocontinuous functor on categories of opens. -/
instance functor_isCocontinuous (hf : IsOpenMap f) :
    hf.functor.IsCocontinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) := sorry

/-- Example 7.21.4 (00XQ): the cocontinuous sheaf direct image induced by an open map agrees
with its usual sheaf direct image. -/
@[stacks 00XQ]
noncomputable def cocontinuousPushforwardIso (hf : IsOpenMap f) :
    hf.functor.sheafPushforwardCocontinuous (Type w)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) ≅
        TopCat.Sheaf.pushforward (Type w) f :=
  (CategoryTheory.Functor.ContinuousRightAdjoint.pushforwardContinuousIso
      hf.functor (Opens.map f) (Type w) hf.adjunction).symm

/-- `cocontinuousPushforwardIso` is the continuous-right-adjoint comparison specialized to an
open map. -/
theorem cocontinuousPushforwardIso_def (hf : IsOpenMap f) :
    cocontinuousPushforwardIso hf =
      (CategoryTheory.Functor.ContinuousRightAdjoint.pushforwardContinuousIso
        hf.functor (Opens.map f) (Type w) hf.adjunction).symm := sorry

/-- The forward and inverse maps of the open-map direct-image comparison compose to the identity. -/
@[simp]
theorem cocontinuousPushforwardIso_hom_inv_id (hf : IsOpenMap f) :
    (cocontinuousPushforwardIso hf).hom ≫ (cocontinuousPushforwardIso hf).inv =
      𝟙 _ := sorry

end IsOpenMap
