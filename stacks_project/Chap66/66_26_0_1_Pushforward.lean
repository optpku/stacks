module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import stacks_project.Chap66.Lemma_66_29_2_Pullback

/-!
# Direct image of modules on algebraic spaces

A morphism of algebraic spaces induces a morphism of small étale ringed topoi. The associated
module direct image is right adjoint to module pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace Modules

/-- The pushforward functor `f_* : Mod(𝒪_X) ⟶ Mod(𝒪_Y)` of sheaves of modules on the small étale
ringed sites of algebraic spaces. -/
def pushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) : X.Modules ⥤ Y.Modules :=
  (ringedToposHom f).modulePushforward

/-- The pushforward of modules along a morphism of algebraic spaces is the module pushforward of
the associated morphism of ringed topoi. -/
theorem pushforward_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    pushforward f = (ringedToposHom f).modulePushforward :=
  rfl

/-- Module pullback along a morphism of algebraic spaces is left adjoint to module pushforward. -/
def pullbackPushforwardAdjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    pullback f ⊣ pushforward f :=
  (ringedToposHom f).moduleAdjunction

end Modules

end AlgebraicGeometry.AlgebraicSpace
