module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Dualizing

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

/- Lemma 48.28.9 -/
@[stacks 0E9W] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.structureSheaf_isFirstComponent :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.hom.left.toShHom).carrier,
        DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase f.hom.left.toShHom).restrict U.isOpenEmbedding))]
      (P : AlgebraicGeometry.Scheme.Compactification.Of Y.obj.left (Over.mk f.hom.left))
      (A : Scheme.DerivedQCoh.PlusRightAdjoint
        (Scheme.Compactification.Of.ambientMorphism P))
      [HomotopyTensorDescends (X.obj.left).toRingedSpace]
      [TensorDescends (X.obj.left).toRingedSpace]
      [IsLocalization (X.obj.left).toRingedSpace]
      [MonoidalCategory
        (RingedSpace.ModuleDerived
          (⊤ : (pullback f.hom.left f.hom.left).Opens).toScheme.toRingedSpace)]
      [(RingedSpace.moduleDerivedPushforward
        (AlgebraicGeometry.Scheme.RelativeDualizingComplex.topDiagonal f.hom.left).toShHom).LaxMonoidal]
      (H : MonoidalClosed
        (RingedSpace.ModuleDerived
          (⊤ : (pullback f.hom.left f.hom.left).Opens).toScheme.toRingedSpace)),
      ∃ C : Scheme.RelativeDualizingComplex f.hom.left
          (⊤ : (pullback f.hom.left f.hom.left).Opens)
          (Scheme.RelativeDualizingComplex.topDiagonal f.hom.left)
          (Scheme.RelativeDualizingComplex.topDiagonal_comp_ι f.hom.left) H,
        C.complex =
          ((Scheme.Compactification.Of.upperShriek f P A.plus).obj
            (Scheme.DerivedQCoh.structureSheafPlus Y.obj.left)).obj.obj)
