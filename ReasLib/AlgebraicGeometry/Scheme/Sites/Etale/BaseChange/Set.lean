/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Sites.LeftExact

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

variable {W X Y S T : Scheme.{u}}

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- requires this option for a private constructor used by an exposed public definition.
set_option backward.privateInPublic true in
/-- Composition of inverse images of set-valued small étale sheaves is canonically
the inverse image of the composite scheme morphism. -/
private noncomputable def setInverseImageCompIso {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) :
    (Scheme.smallEtalePullback (a ≫ b)).sheafPullback (Type (u + 1))
        C.smallEtaleTopology A.smallEtaleTopology ≅
      (Scheme.smallEtalePullback b).sheafPullback (Type (u + 1))
        C.smallEtaleTopology B.smallEtaleTopology ⋙
      (Scheme.smallEtalePullback a).sheafPullback (Type (u + 1))
        B.smallEtaleTopology A.smallEtaleTopology :=
  let siteIso : Scheme.smallEtalePullback b ⋙ Scheme.smallEtalePullback a ≅
      Scheme.smallEtalePullback (a ≫ b) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) a b).symm
  let directImageCompIso := Functor.sheafPushforwardContinuousComp' siteIso
    (Type (u + 1)) C.smallEtaleTopology B.smallEtaleTopology A.smallEtaleTopology
  (Adjunction.leftAdjointCompIso
    ((Scheme.smallEtalePullback b).sheafAdjunctionContinuous (Type (u + 1))
      C.smallEtaleTopology B.smallEtaleTopology)
    ((Scheme.smallEtalePullback a).sheafAdjunctionContinuous (Type (u + 1))
      B.smallEtaleTopology A.smallEtaleTopology)
    ((Scheme.smallEtalePullback (a ≫ b)).sheafAdjunctionContinuous (Type (u + 1))
      C.smallEtaleTopology A.smallEtaleTopology) directImageCompIso).symm

-- Local declaration justification (metaprogramming implementation): Lean's public module
-- elaboration requires this option to use the private composition constructor in an exposed body.
set_option backward.privateInPublic true in
/-- The canonical set-valued base-change component for a cartesian square of schemes. -/
noncomputable def setMap (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (cart : IsPullback h e f g) (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
      S.smallEtaleTopology X.smallEtaleTopology).obj
        (((Scheme.smallEtalePullback g).sheafPushforwardContinuous (Type (u + 1))
          S.smallEtaleTopology T.smallEtaleTopology).obj F) ⟶
      ((Scheme.smallEtalePullback h).sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology Y.smallEtaleTopology).obj
          (((Scheme.smallEtalePullback e).sheafPullback (Type (u + 1))
            T.smallEtaleTopology Y.smallEtaleTopology).obj F) :=
  let squareIso := (setInverseImageCompIso h f).symm ≪≫
    eqToIso (congrArg
      (fun a : Y ⟶ S => (Scheme.smallEtalePullback a).sheafPullback (Type (u + 1))
        S.smallEtaleTopology Y.smallEtaleTopology) cart.w) ≪≫
    setInverseImageCompIso e g
  CategoryTheory.DerivedBaseChange.app
    ((Scheme.smallEtalePullback g).sheafAdjunctionContinuous (Type (u + 1))
      S.smallEtaleTopology T.smallEtaleTopology)
    ((Scheme.smallEtalePullback h).sheafAdjunctionContinuous (Type (u + 1))
      X.smallEtaleTopology Y.smallEtaleTopology) squareIso F

end AlgebraicGeometry.Scheme.Etale.BaseChange

end
