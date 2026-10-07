module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing.ProperFlat

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.StructuredArrow
open DerivedCategory.Plus.CohomologyIn
open RingedSpace
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Scheme.Compactification
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Compactification
namespace Of

/-- A dualizing complex is preserved by a specified upper-shriek model for a
finite-type separated morphism over a Noetherian scheme. -/
theorem upperShriek_isDualizingComplex
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (a : DerivedQCoh (Over.left Y.obj) ⥤ DerivedQCoh P.obj.right.left)
    (aAdjunction : DerivedQCoh.pushforwardCohomologyIn P.obj.right.hom ⊣ a)
    (aPlus : DerivedQCoh.Plus (Over.left Y.obj) ⥤
      DerivedQCoh.Plus P.obj.right.left)
    (aPlusCompatibility :
      aPlus ⋙ DerivedCategory.Plus.CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty P.obj.right.left.toRingedSpace) ≅
        toUnbounded (quasiCoherentModuleProperty (Over.left Y.obj)) ⋙
          a ⋙ DerivedQCoh.inclusion P.obj.right.left)
    (K : DerivedQCoh.Plus (Over.left Y.obj)) (hK : IsDualizingComplex K.obj.obj) :
    IsDualizingComplex ((upperShriek f P aPlus).obj K).obj.obj := sorry

namespace UpperShriek

/-- For a flat morphism of finite-type separated schemes over a Noetherian base,
the upper-shriek image of the derived structure sheaf is the complex underlying
a relative dualizing complex for the morphism. -/
theorem structureSheaf_isFirstComponent
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends (X.obj.left).toRingedSpace]
    [TensorDescends (X.obj.left).toRingedSpace]
    [IsLocalization (X.obj.left).toRingedSpace]
    [MonoidalCategory
      (RingedSpace.ModuleDerived
        (⊤ : (pullback f.hom.left f.hom.left).Opens).toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward
      (RelativeDualizingComplex.topDiagonal f.hom.left).toShHom).LaxMonoidal]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived
        (⊤ : (pullback f.hom.left f.hom.left).Opens).toScheme.toRingedSpace)) :
    ∃ C : Scheme.RelativeDualizingComplex f.hom.left
        (⊤ : (pullback f.hom.left f.hom.left).Opens)
        (RelativeDualizingComplex.topDiagonal f.hom.left)
        (RelativeDualizingComplex.topDiagonal_comp_ι f.hom.left) H,
      C.complex =
        ((upperShriek f P A.plus).obj
          (DerivedQCoh.structureSheafPlus Y.obj.left)).obj.obj := sorry

end UpperShriek

end Of
end Compactification
end Scheme
end AlgebraicGeometry
