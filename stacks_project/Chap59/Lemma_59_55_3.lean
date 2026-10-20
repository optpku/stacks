module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Finite
public import stacks_project.Chap59.Lemma_59_51_9_PushforwardSystem

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1)))

/-- The canonical comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` for a cartesian
square of schemes, retained as a compatibility specialization of `BaseChange.setMap`. -/
noncomputable def finiteBaseChangeHom :
    pullbackAlong g (pushforwardAlong f F) ⟶
      pushforwardAlong f' (pullbackAlong g' F) :=
  BaseChange.setMap g f' g' f h_cart.flip F

/- Lemma 59.55.3: direct image along a finite morphism commutes with inverse
image for every set-valued small étale sheaf in a cartesian square of schemes. -/
@[stacks 0959] #check (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap_isIso :
  ∀ {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) [IsFinite f],
    IsIso (finiteBaseChangeHom f g f' g' h_cart F))

end AlgebraicGeometry.Scheme.Etale

end

end
