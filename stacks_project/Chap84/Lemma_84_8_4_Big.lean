/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import stacks_project.Chap73.Lemma_73_4_7_Relocalization

/-!
# Big étale sheaf functors on algebraic spaces

This leaf packages the slice-site functors associated with a morphism of
algebraic spaces on the big étale topology. The underlying functors are the
canonical postcomposition and pullback functors on over-categories.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace
namespace Etale
namespace Big

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Postcomposition on the big étale slice categories. -/
abbrev map (f : Y ⟶ X) : Over Y ⥤ Over X :=
  Over.map f

/-- Pullback on the big étale slice categories. -/
abbrev pullback (f : Y ⟶ X) : Over X ⥤ Over Y :=
  Over.pullback f

/-- The canonical postcomposition-pullback adjunction on big étale slices. -/
abbrev mapPullbackAdjunction (f : Y ⟶ X) :
    map f ⊣ pullback f :=
  Over.mapPullbackAdj f

/-- Postcomposition admits left Kan extensions of type-valued presheaves on the
source slice. -/
instance map_op_hasLeftKanExtension (f : Y ⟶ X)
    (P : (Over Y)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasLeftKanExtension P := sorry

/-- Postcomposition admits pointwise right Kan extensions of type-valued
presheaves on the source slice. -/
instance map_op_hasPointwiseRightKanExtension (f : Y ⟶ X)
    (P : (Over Y)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasPointwiseRightKanExtension P := sorry

/-- The inverse-image functor on big étale sheaves. -/
abbrev inverseImage (f : Y ⟶ X) :
    Sheaf (overEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology Y) (Type (u + 1)) :=
  (map f).sheafPushforwardContinuous (Type (u + 1))
    (overEtaleTopology Y) (overEtaleTopology X)

/-- The direct-image functor on big étale sheaves, presented by postcomposition. -/
abbrev directImage (f : Y ⟶ X) :
    Sheaf (overEtaleTopology Y) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology X) (Type (u + 1)) :=
  (map f).sheafPushforwardCocontinuous (Type (u + 1))
    (overEtaleTopology Y) (overEtaleTopology X)

/-- Inverse image of big étale sheaves preserves finite limits. -/
instance inverseImage_preservesFiniteLimits (f : Y ⟶ X) :
    PreservesFiniteLimits (inverseImage f) := sorry

/-- The bundled morphism of topoi presented by big étale postcomposition. -/
noncomputable def morphismOfTopoi (f : Y ⟶ X) :
    MorphismOfTopoiIn (overEtaleTopology X) (overEtaleTopology Y) where
  inverseImageFunctor :=
    LeftExactFunctor.of (inverseImage f)
  pushforward := directImage f
  adjunction :=
    (map f).sheafAdjunctionCocontinuous (Type (u + 1))
      (overEtaleTopology Y) (overEtaleTopology X)

/-- The inverse-image projection of the bundled big étale morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : Y ⟶ X) :
    (morphismOfTopoi f)⁻¹ = inverseImage f := sorry

/-- The direct-image projection of the bundled big étale morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : Y ⟶ X) :
    (morphismOfTopoi f).pushforward = directImage f := sorry

end Big
end Etale
end AlgebraicSpace
end AlgebraicGeometry
