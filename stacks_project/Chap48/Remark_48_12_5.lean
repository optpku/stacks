/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing
import StacksCheckRecall

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
  (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackTensorDualityNatTrans :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      [HomotopyTensorDescends Y.toRingedSpace]
      [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (fAdj : pushforwardCohomologyIn f ⊣ a),
      pullback f ⋙ tensorRight (a.obj (structureSheaf Y)) ⟶ a)

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackTensorDualityMapIsIsoOfProperFlat :
    ∀ {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
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
      (fAdj : pushforwardCohomologyIn f ⊣ a) (K : DerivedQCoh Y),
      IsIso (pullbackTensorDualityMap f a fAdj K))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeDualizingTrace_commSq :
    ∀ {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
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
      (fAdj : pushforwardCohomologyIn f ⊣ a) (K : DerivedQCoh Y),
      CommSq
        ((pushforwardCohomologyIn f).map (pullbackTensorDualityMap f a fAdj K))
        (projectionFormulaIso f K (relativeDualizingComplex f a fAdj)).hom
        (fAdj.counit.app K)
        (tensorCounitToUnit f a fAdj K))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeDualizingBaseChangeMap_isIso :
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
      IsIso (relativeDualizingBaseChangeMap f g a a' fAdj f'Adj))

/- Remark 48.12.5: for a proper flat finitely presented morphism to a quasi-compact
quasi-separated scheme, the relative dualizing complex is the right adjoint applied to
the structure sheaf, it induces every counit through the projection formula, and its
complex and trace commute with arbitrary quasi-compact quasi-separated base change. -/
@[stacks 0B6S] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeDualizingTrace_baseChange :
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
      (BaseChange.map
            (CategoryTheory.Limits.pullback.fst f g)
            (CategoryTheory.Limits.pullback.snd f g) f g
            (CategoryTheory.IsPullback.of_hasPullback f g).toCommSq).app
            (relativeDualizingComplex f a fAdj) ≫
          (pushforwardCohomologyIn (CategoryTheory.Limits.pullback.snd f g)).map
            (relativeDualizingBaseChangeMap f g a a' fAdj f'Adj) ≫
        relativeDualizingTrace (CategoryTheory.Limits.pullback.snd f g) a' f'Adj =
      (pullback g).map (relativeDualizingTrace f a fAdj) ≫
        (pullbackStructureSheafIso g).hom)

end AlgebraicGeometry.Scheme.DerivedQCoh
