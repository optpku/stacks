module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafSystem.Pushforward

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite

noncomputable section

universe uI u

namespace AlgebraicGeometry.Scheme.Etale
namespace SheafSystem

variable {I : Type uI} [Preorder I]
variable {D : PreorderInverseSystem I Scheme.{u}}
variable {c : Cone D}

/- Lemma 59.51.9 (1): canonical compatible projection pushforwards. -/
@[stacks 0EYN] #check (AlgebraicGeometry.Scheme.Etale.SheafSystem.pushforwardSystem_spec :
  ∀ (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) {i j : I} (hij : i ≤ j),
    (pushforwardSystem F).obj i = stagePushforward F i ∧
      (pushforwardSystem F).transition hij = stageTransition F hij)

/- Lemma 59.51.9 (2): recovery by the colimit of pulled-back projection pushforwards. -/
@[stacks 0EYN] #check (AlgebraicGeometry.Scheme.Etale.SheafSystem.counitCocone_isColimit :
  ∀ [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.transitionMap hij)]
    (hc : IsLimit c)
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))),
    Nonempty (IsColimit (counitCocone F)))

/- The chosen-colimit comparison remains available as a companion result. -/
#check (comparison_isIso :
  ∀ [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.transitionMap hij)]
    [HasColimitsOfShape I (Sheaf c.pt.smallEtaleTopology (Type (u + 1)))]
    (hc : IsLimit c)
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))),
    IsIso (comparison F))

end SheafSystem
end AlgebraicGeometry.Scheme.Etale
