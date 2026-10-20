module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.ProjectionFormula
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Duality
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.InternalHom

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Over CategoryTheory.StructuredArrow
open DerivedCategory.Plus.CohomologyIn
open RingedSite.Hom.DerivedAdjunction RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

/-- Internal Hom from a bounded-below coherent complex into a dualizing complex has
quasicoherent cohomology. -/
theorem dualOfCoherent_isQuasicoherent
    {S : Scheme.{u}} [IsNoetherian S]
    {Y : Scheme.FiniteTypeSeparatedOver S}
    [MonoidalCategory (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace)]
    (H_Y : MonoidalClosed (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace))
    (K M : DerivedQCoh.Plus Y.obj.left)
    (hK : IsDualizingComplex K.obj.obj)
    (hM_coherent : DerivedCategory.Plus.cohomologyIn
      (SheafOfModules.isCoherent Y.obj.left.toRingedSpace.ringCatSheaf) M.obj) :
    DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace)
      ((H_Y.ihomOf M.obj.obj).obj K.obj.obj) := sorry

/-- The canonical upper-shriek duality morphism obtained from a compactification,
projection formula, and compatibility of pullback with internal Hom. -/
noncomputable def dualityMap
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [HomotopyTensorDescends (Of.ambient P).toRingedSpace]
    [TensorDescends (Of.ambient P).toRingedSpace]
    [IsLocalization (Of.ambient P).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism P).toShHom)]
    [ambientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism P).toShHom)]
    [interiorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (Of.ι P).toShHom)]
    (H_Y : MonoidalClosed (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace))
    (H_P : MonoidalClosed
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace))
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.obj.left.toRingedSpace))
    (K M : DerivedQCoh.Plus Y.obj.left)
    (hK : IsDualizingComplex K.obj.obj)
    (hM_coherent : DerivedCategory.Plus.cohomologyIn
      (SheafOfModules.isCoherent Y.obj.left.toRingedSpace.ringCatSheaf) M.obj) :
    ((upperShriek f P A.plus).obj M).obj.obj ⟶
      (H_X.ihomOf
        ((RingedSpace.modulePullbackDerived f.hom.left.toShHom).obj
          ((H_Y.ihomOf M.obj.obj).obj K.obj.obj))).obj
        ((upperShriek f P A.plus).obj K).obj.obj :=
  let qY := RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace
  let MY := (toUnbounded qY).obj M
  let KY := (toUnbounded qY).obj K
  let DYM : DerivedQCoh Y.obj.left :=
    ⟨(H_Y.ihomOf M.obj.obj).obj K.obj.obj,
      dualOfCoherent_isQuasicoherent H_Y K M hK hM_coherent⟩
  let ev : DerivedQCoh.tensorObj DYM MY ⟶ KY :=
    ⟨(DerivedQCoh.tensorObjIsoTensor DYM MY).hom ≫
      (β_ DYM.obj MY.obj).hom ≫
      (MonoidalClosed.adjunctionOf H_Y MY.obj).counit.app KY.obj⟩
  let adjointMap : (A.right.obj MY).obj ⟶
      (H_P.ihomOf ((DerivedQCoh.pullback (ambientMorphism P)).obj DYM).obj).obj
        (A.right.obj KY).obj :=
    (MonoidalClosed.adjunctionOf H_P
      ((DerivedQCoh.pullback (ambientMorphism P)).obj DYM).obj).homEquiv _ _
        ((DerivedQCoh.tensorObjIsoTensor
            ((DerivedQCoh.pullback (ambientMorphism P)).obj DYM)
            (A.right.obj MY)).inv ≫
          (DerivedQCoh.pullbackTensorRightAdjointMap
            (ambientMorphism P) A.right A.adjunction DYM MY).hom ≫
          (A.right.map ev).hom)
  let factorIso := (DerivedQCoh.inclusion X.obj.left).mapIso
    ((pullbackFactorIso f P).app DYM)
  ((restrictionIso f P A).hom.app M).hom ≫
    (RingedSpace.modulePullbackDerived (Of.ι P).toShHom).map adjointMap ≫
    Functor.PullbackInternalHom.comparisonOf
      H_P H_X (RingedSpace.modulePullbackDerived (Of.ι P).toShHom)
      (fun B C ↦ (@Functor.Monoidal.μIso
        (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
          (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
        (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) _
          (RingedSpace.ModuleDerived.monoidalCategory X.obj.left.toRingedSpace)
        (RingedSpace.modulePullbackDerived (Of.ι P).toShHom)
        interiorPullbackMonoidal B C).symm)
      ((DerivedQCoh.pullback (ambientMorphism P)).obj DYM).obj
      (A.right.obj KY).obj ≫
    ((MonoidalClosed.internalHomOf H_X).map factorIso.inv.op).app
      ((RingedSpace.modulePullbackDerived (Of.ι P).toShHom).obj
        (A.right.obj KY).obj) ≫
    (H_X.ihomOf
      ((RingedSpace.modulePullbackDerived f.hom.left.toShHom).obj DYM.obj)).map
      ((restrictionIso f P A).inv.app K).hom

/-- For a dualizing complex `K` and a bounded-below coherent complex `M`, the
canonical morphism `f⁺!M ⟶ Rℋom(Lf^*Rℋom(M, K), f⁺!K)` is invertible. -/
theorem dualityMap_isIso
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [HomotopyTensorDescends (Of.ambient P).toRingedSpace]
    [TensorDescends (Of.ambient P).toRingedSpace]
    [IsLocalization (Of.ambient P).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism P).toShHom)]
    [ambientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism P).toShHom)]
    [interiorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (Of.ι P).toShHom)]
    (H_Y : MonoidalClosed (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace))
    (H_P : MonoidalClosed
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace))
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.obj.left.toRingedSpace))
    (K M : DerivedQCoh.Plus Y.obj.left)
    (hK : IsDualizingComplex K.obj.obj)
    (hM_coherent : DerivedCategory.Plus.cohomologyIn
      (SheafOfModules.isCoherent Y.obj.left.toRingedSpace.ringCatSheaf) M.obj) :
    IsIso (dualityMap f P A H_Y H_P H_X K M hK hM_coherent) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
