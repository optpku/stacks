module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule

/-!
# Morphisms of small étale ringed topoi of algebraic spaces

A morphism of algebraic spaces induces a morphism of small étale ringed topoi.
The associated structure-sheaf unit and first higher direct image of `𝒪` are
the comparison maps used to detect contraction of fibres.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open ReasLibPullback
open MorphismProperty

variable {S : Scheme.{u}}

/-- Injective resolutions exist for module sheaves on the small étale site. -/
instance modules_hasInjectiveResolutions (X : AlgebraicSpace S) :
    HasInjectiveResolutions (Modules X) := sorry

/-- The type-valued sheaf underlying the structure module `𝒪_X` compares with the
underlying structure sheaf of the small étale ringed site. -/
def unitUnderlyingIso (X : AlgebraicSpace S) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
      (SheafOfModules.unit (structureSheaf X)) ≅
      RingedSite.Hom.underlyingStructureSheaf (ringedSite X) :=
  Iso.refl _

namespace Modules

/-- The canonical morphism `𝒪_Y ⟶ f_* 𝒪_X` of `𝒪_Y`-modules associated to a
morphism of algebraic spaces. -/
def unitToPushforwardObjUnit {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit (structureSheaf Y) ⟶
      (ringedToposHom f).modulePushforward.obj (SheafOfModules.unit (structureSheaf X)) :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf Y)
    ((unitUnderlyingIso Y).hom ≫
      (ringedToposHom f).underlyingDirectImageMap ≫
      (ringedToposHom f).toTopos.pushforward.map (unitUnderlyingIso X).inv ≫
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).inv.app
        (SheafOfModules.unit (structureSheaf X)))
    sorry sorry

end Modules

/-- The first higher direct image `R¹ f_* 𝒪_X` of the structure sheaf. -/
def higherDirectImageOne {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Modules Y :=
  (@Functor.rightDerived _ _ _ _ _ _ _ (ringedToposHom f).modulePushforward
      (RingedSite.ToposHom.modulePushforward_additive (ringedToposHom f)) 1).obj
    (SheafOfModules.unit (structureSheaf X))

end AlgebraicGeometry.AlgebraicSpace
