module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.SheafyTrace.Finiteness
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.MonoidalClosed

universe u

/- Remark 86.3.5 (1): in the situation of Lemma 86.3.3, if both derived internal Hom
objects have quasi-coherent cohomology, then the sheafy-trace morphism (86.3.2.1)
is an isomorphism. -/
@[stacks 0GG4] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.sheafyTrace_isIso_of_derivedQCoh :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
      [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
      [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
      [ModuleDerived.HasDerivedAdjunction f]
      [Functor.Monoidal (ModuleDerived.pullback f)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
      (L : DerivedQCoh X) (K : DerivedQCoh Y),
      derivedQuasiCoherentModuleProperty X ((ihom L.obj).obj (a.obj K).obj) →
        derivedQuasiCoherentModuleProperty Y
          ((ihom ((moduleDerivedPushforward f).obj L.obj)).obj K.obj) →
          IsIso (sheafyTraceMap f a adj L K))

/- Remark 86.3.5 (2): the sheafy-trace morphism is an isomorphism if `L` and
`Rf_* L` are perfect. -/
@[stacks 0GG4] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.sheafyTrace_isIso_of_isPerfect :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
      [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
      [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
      [ModuleDerived.HasDerivedAdjunction f]
      [Functor.Monoidal (ModuleDerived.pullback f)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
      (L : DerivedQCoh X) (K : DerivedQCoh Y),
      ModuleDerived.IsPerfect L.obj →
        ModuleDerived.IsPerfect ((moduleDerivedPushforward f).obj L.obj) →
          IsIso (sheafyTraceMap f a adj L K))

/- Remark 86.3.5 (3): the sheafy-trace morphism is an isomorphism if `K` is bounded
below and `L` and `Rf_* L` are pseudo-coherent. -/
@[stacks 0GG4] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.sheafyTrace_isIso_of_isPseudoCoherent :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
      [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
      [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
      [ModuleDerived.HasDerivedAdjunction f]
      [Functor.Monoidal (ModuleDerived.pullback f)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
      (L : DerivedQCoh X) (K : DerivedQCoh Y),
      K.obj.IsBoundedBelow → IsPseudoCoherent X L.obj →
        IsPseudoCoherent Y ((moduleDerivedPushforward f).obj L.obj) →
          IsIso (sheafyTraceMap f a adj L K))
