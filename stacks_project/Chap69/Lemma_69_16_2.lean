module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.AffineComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u

/- Lemma 69.16.2: The canonical associated-module comparison with absolute direct image is an isomorphism. -/
@[stacks 07UZ] #check
  (AlgebraicGeometry.AlgebraicSpace.pushforward_tensorOX :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
      [HasVanishingH1 X] (M : ModuleCat.{u} (globalSectionsRing X)),
      IsIso (tensorOXPushforwardUnit X M))

/- Lemma 69.16.2: The canonical comparison with global sections of the associated module is an isomorphism. -/
@[stacks 07UZ] #check
  (AlgebraicGeometry.AlgebraicSpace.tensorOX_globalSections :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
      [HasVanishingH1 X] (M : ModuleCat.{u} (globalSectionsRing X)),
      IsIso (tensorOXSectionsUnit X M))
