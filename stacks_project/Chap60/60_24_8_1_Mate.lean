module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.BaseChange

@[expose] public section

open CategoryTheory
open RingedSite
open RingedSite.Hom
open RingedSite.Hom.DerivedBaseChange

noncomputable section

universe u v w z

/-- The sheaf-level derived base-change map followed by a specified crystalline pullback
comparison.  This is the reusable mate underlying the source-facing global-sections map. -/
noncomputable def derivedCrystallineBaseChange
    {X' X S' S : RingedSite.{u, v, w}}
    [UnivLE.{max u v, z}]
    (g' : RingedSite.Hom X X') (f' : RingedSite.Hom X' S')
    (f : RingedSite.Hom X S) (g : RingedSite.Hom S S')
    [g'.modulePushforward.{z}.IsRightAdjoint]
    [f'.modulePushforward.{z}.IsRightAdjoint]
    [f.modulePushforward.{z}.IsRightAdjoint]
    [g.modulePushforward.{z}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f') (ModuleQis.{z} X')]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} g) (ModuleQis.{z} S')]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} g') (ModuleQis.{z} X')]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} f) (ModuleQis.{z} S)]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} f') (ModuleQis.{z} S')]
    [DerivedAdjunction.HasPair.{z} f]
    [DerivedAdjunction.HasPair.{z} f']
    (squareIso :
      modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
        modulePullbackDerived.{z} f' ⋙ modulePullbackDerived.{z} g')
    (F' : ModuleDerived.{z} X') (F : ModuleDerived.{z} X)
    (crystallinePullback : (modulePullbackDerived.{z} g').obj F' ⟶ F) :
    (modulePullbackDerived.{z} g).obj ((modulePushforwardDerived.{z} f').obj F') ⟶
      (modulePushforwardDerived.{z} f).obj F :=
  (DerivedBaseChange.map g' f f' g squareIso F') ≫
    (modulePushforwardDerived.{z} f).map crystallinePullback

/-- The sheaf-level mate is the canonical derived base-change map followed by the crystalline
pullback comparison. -/
theorem derivedCrystallineBaseChange_spec
    {X' X S' S : RingedSite.{u, v, w}}
    [UnivLE.{max u v, z}]
    (g' : RingedSite.Hom X X') (f' : RingedSite.Hom X' S')
    (f : RingedSite.Hom X S) (g : RingedSite.Hom S S')
    [g'.modulePushforward.{z}.IsRightAdjoint]
    [f'.modulePushforward.{z}.IsRightAdjoint]
    [f.modulePushforward.{z}.IsRightAdjoint]
    [g.modulePushforward.{z}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f') (ModuleQis.{z} X')]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} g) (ModuleQis.{z} S')]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} g') (ModuleQis.{z} X')]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} f) (ModuleQis.{z} S)]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} f') (ModuleQis.{z} S')]
    [DerivedAdjunction.HasPair.{z} f]
    [DerivedAdjunction.HasPair.{z} f']
    (squareIso :
      modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
        modulePullbackDerived.{z} f' ⋙ modulePullbackDerived.{z} g')
    (F' : ModuleDerived.{z} X') (F : ModuleDerived.{z} X)
    (crystallinePullback : (modulePullbackDerived.{z} g').obj F' ⟶ F) :
    derivedCrystallineBaseChange g' f' f g squareIso F' F crystallinePullback =
      (DerivedBaseChange.map g' f f' g squareIso F') ≫
        (modulePushforwardDerived.{z} f).map crystallinePullback := sorry
