module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.Coherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure

universe u

/- Lemma 75.8.1: Derived pushforward preserves bounded coherent cohomology
when the cohomology sheaves have support proper over a Noetherian target. -/
@[stacks 08GK] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_boundedCoherent_of_properSupport :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (f : X ⟶ Y) [LocallyOfFiniteType f] [IsNoetherian Y]
      (E : ModuleDerived X),
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf X)) E →
      (t.bounded : ObjectProperty (ModuleDerived X)) E →
      (∀ i : ℤ, ClosedSubset.ProperOver f
        (Modules.closedSupport
          ((DerivedCategory.homologyFunctor (Modules X) i).obj E))) →
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent (structureSheaf Y))
          ((Modules.moduleDerivedPushforward f).obj E) ∧
        (t.bounded : ObjectProperty (ModuleDerived Y))
          ((Modules.moduleDerivedPushforward f).obj E))
