module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import Mathlib.CategoryTheory.Functor.EpiMono

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

/-- The direct image of the structure sheaf, viewed as a module on the target
algebraic space. -/
noncomputable abbrev pushforwardStructureModule {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Y.Modules :=
  (pushforward f).obj (SheafOfModules.unit (structureSheaf X) : X.Modules)

/-- The pushforward of the structure sheaf is the image of `𝒪_X` under module
pushforward. -/
theorem pushforwardStructureModule_obj {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    pushforwardStructureModule f =
      (pushforward f).obj (SheafOfModules.unit (structureSheaf X)) :=
  rfl

/-- Module pullback along a morphism of algebraic spaces is left adjoint to module pushforward. -/
def pullbackPushforwardAdjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    pullback f ⊣ pushforward f :=
  ((ringedToposHom f).moduleAdjunction).ofNatIsoLeft (pullbackIsoTopos f).symm

/-- The morphism from a pulled-back module corresponding to a morphism into a pushforward
under the pullback-pushforward adjunction. -/
def adjointToPushforward {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    {ℱ : X.Modules} {ℋ : Z.Modules} (u : ℱ ⟶ (pushforward i).obj ℋ) :
    (pullback i).obj ℱ ⟶ ℋ :=
  ((pullbackPushforwardAdjunction i).homEquiv ℱ ℋ).symm u

/-- Module pullback along a morphism of algebraic spaces is a left adjoint. -/
instance pullback.isLeftAdjoint {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (pullback f).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction f).isLeftAdjoint

/-- Module pushforward along a morphism of algebraic spaces is a right adjoint, hence left
exact. -/
instance pushforward.isRightAdjoint {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (pushforward f).IsRightAdjoint :=
  (pullbackPushforwardAdjunction f).isRightAdjoint

/-- Direct image of module sheaves on algebraic spaces preserves monomorphisms. -/
instance pushforward_preservesMonomorphisms {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (pushforward f).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_adjunction (pullbackPushforwardAdjunction f)

end Modules

/-- The direct image of the structure sheaf as a module on the target. -/
noncomputable abbrev Hom.pushforwardStructureModule {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Y.Modules :=
  Modules.pushforwardStructureModule f

end AlgebraicGeometry.AlgebraicSpace
