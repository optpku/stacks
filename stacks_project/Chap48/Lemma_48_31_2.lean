module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Compactification

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

universe v

/- Lemma 48.31.2 -/
@[stacks 0G4X]
#check (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero_compactificationIso :
  ∀ {X U : Scheme.{v}} (j : U ⟶ X)
    [IsNoetherian X] [IsNoetherian U]
    [IsOpenImmersion j]
    (P : AlgebraicGeometry.Scheme.Compactification.Of X (Over.mk j)),
    AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero j ≅
      @AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.properPushforwardLimAlong
        P.obj.right.left X U P.obj.right.hom
        (AlgebraicGeometry.Scheme.Compactification.Of.ι P)
        (AlgebraicGeometry.Scheme.Compactification.Of.instAmbientIsNoetherian P)
        ‹_› ‹_›
        (AlgebraicGeometry.Scheme.Compactification.Of.instIsProper X (Over.mk j) P)
        (AlgebraicGeometry.Scheme.Compactification.Of.instIsOpenImmersion X (Over.mk j) P)
        (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.isOpenImmersion_compactification_comp
          ‹IsOpenImmersion j› P))
