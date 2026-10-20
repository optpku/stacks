module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)

/-- Canonical Beck–Chevalley comparison
`(smallEtalePullback f).sheafPullback ((smallEtalePullback g).sheafPushforwardContinuous F) ⟶
(smallEtalePullback h).sheafPushforwardContinuous ((smallEtalePullback e).sheafPullback F)`,
with the scheme morphisms ordered as `f g h e`. -/
abbrev etaleSheafBaseChangeMap (h_cart : IsPullback h e f g)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    ((smallEtalePullback f).sheafPullback (Type (u + 1))
        S.smallEtaleTopology X.smallEtaleTopology).obj
      (((smallEtalePullback g).sheafPushforwardContinuous (Type (u + 1))
          S.smallEtaleTopology T.smallEtaleTopology).obj F) ⟶
      ((smallEtalePullback h).sheafPushforwardContinuous (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj
        (((smallEtalePullback e).sheafPullback (Type (u + 1))
            T.smallEtaleTopology Y.smallEtaleTopology).obj F) :=
  AlgebraicGeometry.Scheme.Etale.BaseChange.setMap f h e g h_cart F

/- Lemma 59.87.1: for a cartesian square of schemes with `f` flat, if every object of
`X_étale` admits an étale covering whose maps to `S` factor as quasi-compact morphisms with
geometrically connected fibres onto étale objects of `S`, then for every sheaf of sets `F` on
`T_étale` the comparison `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism. -/
@[stacks 0EZX] #check (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap_isIso_of_flat :
  ∀ {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f] (cart : IsPullback h e f g)
    (h_cover : AlgebraicGeometry.Scheme.Etale.HasConnectedFactorizationCover f)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))),
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap f h e g cart F))

end AlgebraicGeometry.Scheme
