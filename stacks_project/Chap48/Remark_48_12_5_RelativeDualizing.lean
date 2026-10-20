module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeDualizingComplex :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (_ : pushforwardCohomologyIn f ⊣ a),
      DerivedQCoh X)

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeDualizingTrace :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (fAdj : pushforwardCohomologyIn f ⊣ a),
      (pushforwardCohomologyIn f).obj (relativeDualizingComplex f a fAdj) ⟶
        structureSheaf Y)

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeDualizingBaseChangeMap :
    ∀ {X Y' Y : Scheme.{u}}
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
      (f'Adj : pushforwardCohomologyIn (CategoryTheory.Limits.pullback.snd f g) ⊣ a'),
      (pullback (CategoryTheory.Limits.pullback.fst f g)).obj
          (relativeDualizingComplex f a fAdj) ⟶
        relativeDualizingComplex (CategoryTheory.Limits.pullback.snd f g) a' f'Adj)

end AlgebraicGeometry.Scheme.DerivedQCoh
