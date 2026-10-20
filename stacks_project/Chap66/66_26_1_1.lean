module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationAdjunction
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Sheaf.InternalModule

/- 66.26.1.1: Restriction of module sheaves is canonically isomorphic to pullback. -/
@[stacks 03LW] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.restrictFunctorIsoPullback :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      Modules.restrictFunctor f ≅ Modules.pullback f)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.restrictFunctor :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      Y.Modules ⥤ X.Modules)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.restrictFunctorIsoInverseImage :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      Modules.restrictFunctor f ⋙ ToInternal.underlying (structureSheaf X) ≅
        ToInternal.underlying (structureSheaf Y) ⋙ etaleRestrictionSheaf f (Type u))

/- The following comparisons identify underlying module restriction with actual
small-topos inverse image via postcomposition on the small étale sites. These are
canonical natural isomorphisms of functors. The module action is induced by the
identity-on-sections comparison of structure sheaves. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.restrictUnderlyingIsoPostcompose :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      Modules.restrictFunctor f ⋙ ToInternal.underlying (structureSheaf X) ≅
        ToInternal.underlying (structureSheaf Y) ⋙
          (Modules.restrictPostcompose f).sheafPushforwardContinuous (Type u)
            (smallEtaleTopology X) (smallEtaleTopology Y))

#check
  (AlgebraicGeometry.AlgebraicSpace.EtaleTopos.restrictTypeIsoInverseImage :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      (Modules.restrictPostcompose f).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology X) (smallEtaleTopology Y) ≅
        (AlgebraicGeometry.AlgebraicSpace.morphismOfTopoi f).inverseImage)
