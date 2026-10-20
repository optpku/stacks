module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback.Flat

@[expose] public section

open CategoryTheory
open DerivedCategory.Plus.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open DerivedQCoh.Flat

namespace Compactification.Of

/-- For a cartesian square of finite-type separated schemes over a Noetherian
base whose lower horizontal morphism is flat, bounded-below derived pullback
commutes with upper shriek up to natural isomorphism. -/
theorem upperShriek_flatBaseChange_isomorphic
    {S : Scheme.{u}} [IsNoetherian S]
    {X' X Y' Y : FiniteTypeSeparatedOver S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left)
    [Flat g.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (a : DerivedQCoh Y.obj.left ⥤ DerivedQCoh P.obj.right.left)
    (aAdjunction : DerivedQCoh.pushforwardCohomologyIn P.obj.right.hom ⊣ a)
    (aPlus : DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus P.obj.right.left)
    (aPlusCompatibility :
      aPlus ⋙ ambient
          (RingedSpace.quasiCoherentModuleProperty P.obj.right.left.toRingedSpace) ≅
        toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace) ⋙
          a ⋙ DerivedQCoh.inclusion P.obj.right.left)
    (P' : Of Y'.obj.left (Over.mk f'.hom.left))
    (aPrime : DerivedQCoh Y'.obj.left ⥤ DerivedQCoh P'.obj.right.left)
    (aPrimeAdjunction : DerivedQCoh.pushforwardCohomologyIn P'.obj.right.hom ⊣ aPrime)
    (aPrimePlus : DerivedQCoh.Plus Y'.obj.left ⥤ DerivedQCoh.Plus P'.obj.right.left)
    (aPrimePlusCompatibility :
      aPrimePlus ⋙ ambient
          (RingedSpace.quasiCoherentModuleProperty P'.obj.right.left.toRingedSpace) ≅
        toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Y'.obj.left.toRingedSpace) ⋙
          aPrime ⋙ DerivedQCoh.inclusion P'.obj.right.left) :
    IsIsomorphic
      (upperShriek f P aPlus ⋙
        pullbackPlusOfIsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left sq)
      (pullbackPlus g.hom.left ⋙ upperShriek f' P' aPrimePlus) := sorry

end Compactification.Of
end AlgebraicGeometry.Scheme
