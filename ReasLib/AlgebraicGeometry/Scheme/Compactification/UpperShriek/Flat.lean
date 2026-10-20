module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Homothety
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

/-- For a flat morphism of finite-type separated schemes over a Noetherian base, the
compactification upper-shriek dualizing object is perfect relative to the target. -/
theorem dualizingObject_isPerfectRelativeTo_of_flat
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.hom.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.hom.left.toShHom).restrict U.isOpenEmbedding))]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    ModuleDerived.IsPerfectRelativeTo f.hom.left (dualizingObject f P A).obj := sorry

/-- For a flat morphism of finite-type separated schemes over a Noetherian base, the
canonical homothety of the compactification upper-shriek dualizing object is an isomorphism. -/
@[instance]
theorem dualizingHomothety_isIso_of_flat
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends (X.obj.left).toRingedSpace]
    [TensorDescends (X.obj.left).toRingedSpace]
    [IsLocalization (X.obj.left).toRingedSpace]
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived (X.obj.left).toRingedSpace)) :
    IsIso (dualizingHomothety f P A H_X) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
