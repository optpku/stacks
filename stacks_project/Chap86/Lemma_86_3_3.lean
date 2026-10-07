module

public import stacks_project.Chap86.Lemma_86_3_3_SheafyTrace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal

universe u

/- Lemma 86.3.3: for a morphism `f : X ⟶ Y` of quasi-compact quasi-separated
algebraic spaces over a scheme `S`, with `a` a right adjoint of
`Rf_* : DerivedQCoh X ⥤ DerivedQCoh Y`, and for `L` in `DerivedQCoh X` and
`K` in `DerivedQCoh Y`, the sheafy-trace map (86.3.2.1) becomes an isomorphism
after applying the right adjoint of `inclusion Y` (the functor `DQ_Y` of
Derived Categories of Spaces, Section 75.19). -/
@[stacks 0E58] #check
  (coheratedSheafyTraceMapIsIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
      [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
      [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
      [Functor.LaxMonoidal (moduleDerivedPushforward f)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
      (L : DerivedQCoh X) (K : DerivedQCoh Y),
      IsIso (coheratedSheafyTraceMap f a adj L K))
