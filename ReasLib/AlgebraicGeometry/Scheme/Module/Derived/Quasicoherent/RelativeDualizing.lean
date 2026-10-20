module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.ProperFlat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.BaseChange.ProperFlat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a chosen right adjoint to derived pushforward, the relative dualizing complex is
the value of that right adjoint on the derived structure sheaf. -/
noncomputable def relativeDualizingComplex
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (_ : pushforwardCohomologyIn f ⊣ a) : DerivedQCoh X :=
  a.obj (structureSheaf Y)

/-- The trace of a relative dualizing complex is the counit of the chosen adjunction at
the derived structure sheaf. -/
noncomputable def relativeDualizingTrace
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (fAdj : pushforwardCohomologyIn f ⊣ a) :
    (pushforwardCohomologyIn f).obj (relativeDualizingComplex f a fAdj) ⟶
      structureSheaf Y :=
  fAdj.counit.app (structureSheaf Y)

/-- Every counit map of a proper flat finitely presented morphism is induced from the
relative dualizing trace through the projection formula. -/
theorem relativeDualizingTrace_commSq
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace]
    [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (fAdj : pushforwardCohomologyIn f ⊣ a) (K : DerivedQCoh Y) :
    CommSq
      ((pushforwardCohomologyIn f).map (pullbackTensorDualityMap f a fAdj K))
      (projectionFormulaIso f K (relativeDualizingComplex f a fAdj)).hom
      (fAdj.counit.app K)
      (tensorCounitToUnit f a fAdj K) := sorry

/-- The canonical base-change comparison from the pullback of a relative dualizing
complex to the relative dualizing complex of the base-changed morphism. -/
noncomputable def relativeDualizingBaseChangeMap
    {X Y' Y : Scheme.{u}}
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [HomotopyTensorDescends Y'.toRingedSpace]
    [TensorDescends Y'.toRingedSpace]
    [IsLocalization Y'.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace]
    [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g.toShHom)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (a' : DerivedQCoh Y' ⥤ DerivedQCoh (CategoryTheory.Limits.pullback f g))
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn (CategoryTheory.Limits.pullback.snd f g) ⊣ a') :
    (pullback (CategoryTheory.Limits.pullback.fst f g)).obj
        (relativeDualizingComplex f a fAdj) ⟶
      relativeDualizingComplex (CategoryTheory.Limits.pullback.snd f g) a' f'Adj :=
  ((DerivedBaseChange.mapOfRight
      (pullbackPushforwardAdjunction g)
      (pullbackPushforwardAdjunction (CategoryTheory.Limits.pullback.fst f g))
      (rightMateIsoOfFlatLeft f g a a' fAdj f'Adj).inv).app (structureSheaf Y)) ≫
    a'.map (pullbackStructureSheafIso g).hom

/-- The canonical relative-dualizing base-change comparison for a proper flat finitely
presented morphism is an isomorphism. -/
theorem relativeDualizingBaseChangeMap_isIso
    {X Y' Y : Scheme.{u}}
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [HomotopyTensorDescends Y'.toRingedSpace]
    [TensorDescends Y'.toRingedSpace]
    [IsLocalization Y'.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace]
    [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g.toShHom)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (a' : DerivedQCoh Y' ⥤ DerivedQCoh (CategoryTheory.Limits.pullback f g))
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn (CategoryTheory.Limits.pullback.snd f g) ⊣ a') :
    IsIso (relativeDualizingBaseChangeMap f g a a' fAdj f'Adj) := sorry

/-- Under canonical proper-flat base change, the trace of the base-changed relative
dualizing complex is the pullback of the original trace. -/
theorem relativeDualizingTrace_baseChange
    {X Y' Y : Scheme.{u}}
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [HomotopyTensorDescends Y'.toRingedSpace]
    [TensorDescends Y'.toRingedSpace]
    [IsLocalization Y'.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace]
    [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g.toShHom)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (a' : DerivedQCoh Y' ⥤ DerivedQCoh (CategoryTheory.Limits.pullback f g))
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn (CategoryTheory.Limits.pullback.snd f g) ⊣ a') :
    (BaseChange.map
          (CategoryTheory.Limits.pullback.fst f g)
          (CategoryTheory.Limits.pullback.snd f g) f g
          (CategoryTheory.IsPullback.of_hasPullback f g).toCommSq).app
          (relativeDualizingComplex f a fAdj) ≫
        (pushforwardCohomologyIn (CategoryTheory.Limits.pullback.snd f g)).map
          (relativeDualizingBaseChangeMap f g a a' fAdj f'Adj) ≫
      relativeDualizingTrace (CategoryTheory.Limits.pullback.snd f g) a' f'Adj =
    (pullback g).map (relativeDualizingTrace f a fAdj) ≫
      (pullbackStructureSheafIso g).hom := sorry

/-- The relative dualizing complex of a proper flat finitely presented morphism over a
quasi-compact quasi-separated scheme is perfect relative to the base. -/
theorem relativeDualizingComplex_isPerfectRelativeTo
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a) :
    ModuleDerived.IsPerfectRelativeTo f
      (relativeDualizingComplex f a aAdjunction).obj := sorry

/-- The derived pushforward of the relative dualizing complex of a proper flat finitely
presented morphism has zero cohomology sheaves in every positive degree. -/
theorem relativeDualizingPushforward_cohomology_isZero_of_pos
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (i : ℤ) (hi : 0 < i) :
    IsZero (RingedSpace.ModuleDerived.cohomologySheaf
      ((pushforwardCohomologyIn f).obj
        (relativeDualizingComplex f a aAdjunction)).obj i) := sorry

/-- The canonical homothety from the tensor unit to the derived endomorphism object of
a relative dualizing complex is an isomorphism. -/
@[instance]
theorem relativeDualizingHomothetyIsIso
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)) :
    let ω := (relativeDualizingComplex f a aAdjunction).obj
    IsIso (@MonoidalClosed.curry'
      (RingedSpace.ModuleDerived X.toRingedSpace) _ _ ω ω (H.closed ω) (𝟙 ω)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
