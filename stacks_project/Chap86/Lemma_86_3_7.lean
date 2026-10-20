module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.GlobalTrace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.MonoidalClosed

universe u

/- Lemma 86.3.7: for a morphism `f : X ⟶ Y` of quasi-compact quasi-separated
algebraic spaces over a scheme `S`, with `a` a right adjoint of
`Rf_* : DerivedQCoh X ⥤ DerivedQCoh Y`, and for `L` in `DerivedQCoh X` and
`K` in `DerivedQCoh Y`, the sheafy-trace map (86.3.2.1) induces an isomorphism
`RHom_X(L, a(K)) ⟶ RHom_Y(Rf_* L, K)` of global derived Homs. -/
@[stacks 0E59] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.globalTraceMapIsIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
      [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
      [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
      [ModuleDerived.HasDerivedAdjunction f]
      [Functor.Monoidal (ModuleDerived.pullback f)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
      (L : DerivedQCoh X) (K : DerivedQCoh Y),
      IsIso (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.globalTraceMap f a adj L K))
