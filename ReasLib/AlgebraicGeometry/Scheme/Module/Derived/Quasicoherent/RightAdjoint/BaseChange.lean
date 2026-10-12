/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange.Trace

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open CategoryTheory.MonoidalCategory
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The canonical comparison between the two iterated derived pullbacks around a
commutative square of schemes. -/
noncomputable def pullbackSquareAppIso {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : CommSq g' f' f g) (K : DerivedQCoh Y) :
    (pullback g').obj ((pullback f).obj K) ≅
      (pullback f').obj ((pullback g).obj K) :=
  pullbackCompAppIso g' f
      (RingedSpace.modulePullbackDerived.compComparison_isIso g'.toShHom f.toShHom) K ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ (pullback h).obj K) sq.w) ≪≫
    (pullbackCompAppIso f' g
      (RingedSpace.modulePullbackDerived.compComparison_isIso f'.toShHom g.toShHom) K).symm

/-- Derived pullback carries the derived structure sheaf to the derived structure sheaf. -/
noncomputable def pullbackStructureSheafIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace] [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)] :
    (pullback f).obj (structureSheaf Y) ≅ structureSheaf X :=
  (ModuleDerived.quasicoherentProperty X).fullyFaithfulι.preimageIso
    ((pullback.inclusionIso f).app (structureSheaf Y) ≪≫
      (RingedSpace.modulePullbackDerived f.toShHom).mapIso (structureSheafUnitIso Y) ≪≫
      (Functor.Monoidal.εIso (RingedSpace.modulePullbackDerived f.toShHom)).symm ≪≫
      (structureSheafUnitIso X).symm)

/-- The base-change map on chosen right adjoints obtained as the inverse mate of a dual
base-change isomorphism. -/
noncomputable def rightAdjointBaseChangeMap
    {X' X Y' Y : Scheme.{u}}
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (g : Y' ⟶ Y)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (dualBaseChangeIso : a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (K : DerivedQCoh Y) :
    (pullback g').obj (a.obj K) ⟶ a'.obj ((pullback g).obj K) :=
  (CategoryTheory.DerivedBaseChange.mapOfRight
    (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction g')
    dualBaseChangeIso.inv).app K

/-- The left vertical map in the tensor-duality base-change square: distribute pullback
over tensor, compare the two iterated pullbacks, and apply right-adjoint base change to the
structure-sheaf factor. -/
noncomputable def pullbackTensorDualityBaseChangeMap
    {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends X'.toRingedSpace] [TensorDescends X'.toRingedSpace]
    [IsLocalization X'.toRingedSpace]
    [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y'.toRingedSpace] [TensorDescends Y'.toRingedSpace]
    [IsLocalization Y'.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace] [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g.toShHom)]
    (sq : CommSq g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (dualBaseChangeIso : a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (K : DerivedQCoh Y) :
    (pullback g').obj
        (tensorObj ((pullback f).obj K) (a.obj (structureSheaf Y))) ⟶
      tensorObj ((pullback f').obj ((pullback g).obj K))
        (a'.obj (structureSheaf Y')) :=
  (pullbackTensorIso g' ((pullback f).obj K) (a.obj (structureSheaf Y))).hom ≫
    ⟨(tensorObjIsoTensor ((pullback g').obj ((pullback f).obj K))
          ((pullback g').obj (a.obj (structureSheaf Y)))).hom ≫
      ((pullbackSquareAppIso g' f' f g sq K).hom.hom ⊗ₘ
        (rightAdjointBaseChangeMap g' g a a' dualBaseChangeIso (structureSheaf Y) ≫
          a'.map (pullbackStructureSheafIso g).hom).hom) ≫
      (tensorObjIsoTensor ((pullback f').obj ((pullback g).obj K))
        (a'.obj (structureSheaf Y'))).inv⟩

/-- The tensor-duality base-change map is the canonical pullback-tensor comparison,
followed by the square and right-adjoint base-change comparisons on the two factors. -/
theorem pullbackTensorDualityBaseChangeMap_spec
    {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends X'.toRingedSpace] [TensorDescends X'.toRingedSpace]
    [IsLocalization X'.toRingedSpace]
    [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y'.toRingedSpace] [TensorDescends Y'.toRingedSpace]
    [IsLocalization Y'.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace] [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g.toShHom)]
    (sq : CommSq g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (dualBaseChangeIso : a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (K : DerivedQCoh Y) :
    pullbackTensorDualityBaseChangeMap g' f' f g sq a a' dualBaseChangeIso K =
      (pullbackTensorIso g' ((pullback f).obj K) (a.obj (structureSheaf Y))).hom ≫
        ⟨(tensorObjIsoTensor ((pullback g').obj ((pullback f).obj K))
            ((pullback g').obj (a.obj (structureSheaf Y)))).hom ≫
          ((pullbackSquareAppIso g' f' f g sq K).hom.hom ⊗ₘ
            (rightAdjointBaseChangeMap g' g a a' dualBaseChangeIso (structureSheaf Y) ≫
              a'.map (pullbackStructureSheafIso g).hom).hom) ≫
          (tensorObjIsoTensor ((pullback f').obj ((pullback g).obj K))
            (a'.obj (structureSheaf Y'))).inv⟩ := sorry

/-- The tensor-duality comparison commutes with derived pullback and right-adjoint base change
for a Tor-independent cartesian square. -/
theorem pullbackTensorDualityMap_baseChange
    {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends X'.toRingedSpace] [TensorDescends X'.toRingedSpace]
    [IsLocalization X'.toRingedSpace]
    [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y'.toRingedSpace] [TensorDescends Y'.toRingedSpace]
    [IsLocalization Y'.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace] [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g.toShHom)]
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y) :
    let dualBaseChangeIso :=
      @asIso _ _ _ _
        (BaseChange.rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
        (BaseChange.rightMate_isIso_of_torIndependent
          g' f' f g sq a a' fAdj f'Adj hTor)
    CommSq
      ((pullback g').map (pullbackTensorDualityMap f a fAdj K))
      (pullbackTensorDualityBaseChangeMap
        g' f' f g sq.toCommSq a a' dualBaseChangeIso K)
      (rightAdjointBaseChangeMap g' g a a' dualBaseChangeIso K)
      (pullbackTensorDualityMap f' a' f'Adj ((pullback g).obj K)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
