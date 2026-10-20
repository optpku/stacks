module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.ProjectionFormula
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

/-- The homothety from the derived structure sheaf to the derived endomorphism object of the
compactification model of the upper-shriek dualizing object. -/
noncomputable def dualizingHomothety
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends (X.obj.left).toRingedSpace]
    [TensorDescends (X.obj.left).toRingedSpace]
    [IsLocalization (X.obj.left).toRingedSpace]
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived (X.obj.left).toRingedSpace)) :
    (DerivedQCoh.structureSheaf X.obj.left).obj ⟶
      (MonoidalClosed.ihomOf H_X (dualizingObject f P A).obj).obj
        (dualizingObject f P A).obj :=
  (DerivedQCoh.structureSheafUnitIso X.obj.left).hom ≫
    (@MonoidalClosed.curry'
      (RingedSpace.ModuleDerived (X.obj.left).toRingedSpace) _ _
      (dualizingObject f P A).obj (dualizingObject f P A).obj
      (H_X.closed (dualizingObject f P A).obj) (𝟙 (dualizingObject f P A).obj))

/-- The homothety is the structure-sheaf unit comparison followed by the closed-monoidal curry
of the identity of the dualizing object. -/
theorem dualizingHomothety_def
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends (X.obj.left).toRingedSpace]
    [TensorDescends (X.obj.left).toRingedSpace]
    [IsLocalization (X.obj.left).toRingedSpace]
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived (X.obj.left).toRingedSpace)) :
    dualizingHomothety f P A H_X =
      (DerivedQCoh.structureSheafUnitIso X.obj.left).hom ≫
        (@MonoidalClosed.curry'
          (RingedSpace.ModuleDerived (X.obj.left).toRingedSpace) _ _
          (dualizingObject f P A).obj (dualizingObject f P A).obj
          (H_X.closed (dualizingObject f P A).obj)
          (𝟙 (dualizingObject f P A).obj)) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
