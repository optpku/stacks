module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.OpenCohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

/- Remark 36.7.7 (Warning): on an affine scheme, the canonical degree-one comparison from
derived quasicoherent sections on a quasi-compact open to cohomology of the underlying additive
sheaf need not be invertible, even at an injective module where its source vanishes. -/
@[stacks 0CRY] #check
  (AlgebraicGeometry.Scheme.QCoh.existsAffineOpenDerivedSectionsComparison_not_isIso :
    ∃ (A : CommRingCat.{u}) (I : ModuleCat A) (U : CompactOpens (Spec A).carrier),
      Injective I ∧
        IsZero
          (((AlgebraicGeometry.Scheme.QCoh.openSectionsFunctor
            (Spec A) U.toOpens).rightDerived 1).obj
              ((AlgebraicGeometry.tildeEquiv :
                ModuleCat A ≌ Scheme.QCoh (Spec A)).functor.obj I)) ∧
        ¬ IsZero
          ((AlgebraicGeometry.Scheme.QCoh.openCohomologyFunctor
            (Spec A) U.toOpens 1).obj
              ((AlgebraicGeometry.tildeEquiv :
                ModuleCat A ≌ Scheme.QCoh (Spec A)).functor.obj I)) ∧
        ¬ IsIso
          ((AlgebraicGeometry.Scheme.QCoh.openDerivedSectionsComparison
            (Spec A) U.toOpens 1).app
              ((AlgebraicGeometry.tildeEquiv :
                ModuleCat A ≌ Scheme.QCoh (Spec A)).functor.obj I)))

/- The canonical comparison is defined for every scheme, open subset, and degree. -/
#check (AlgebraicGeometry.Scheme.QCoh.openDerivedSectionsComparison :
  ∀ (X : Scheme.{u}) (U : TopologicalSpace.Opens X.carrier) (i : ℕ),
    (AlgebraicGeometry.Scheme.QCoh.openSectionsFunctor X U).rightDerived i ⟶
      AlgebraicGeometry.Scheme.QCoh.openCohomologyFunctor X U i)

/- The affine counterexample retains the injective module, quasi-compact open, vanishing
derived-sections source, and nonvanishing underlying-sheaf cohomology target. -/
#check (AlgebraicGeometry.Scheme.QCoh.existsAffineDerivedSectionsCounterexample :
  ∃ (A : CommRingCat.{u}) (I : ModuleCat A) (U : CompactOpens (Spec A).carrier),
    Injective I ∧
      IsZero
        (((AlgebraicGeometry.Scheme.QCoh.openSectionsFunctor
          (Spec A) U.toOpens).rightDerived 1).obj
            ((AlgebraicGeometry.tildeEquiv :
              ModuleCat A ≌ Scheme.QCoh (Spec A)).functor.obj I)) ∧
      ¬ IsZero
        ((AlgebraicGeometry.Scheme.QCoh.openCohomologyFunctor
          (Spec A) U.toOpens 1).obj
            ((AlgebraicGeometry.tildeEquiv :
              ModuleCat A ≌ Scheme.QCoh (Spec A)).functor.obj I)))

/- A comparison from degree-one derived quasicoherent sections to underlying-sheaf cohomology
cannot be invertible at an object where its source vanishes and its target does not. -/
#check (AlgebraicGeometry.Scheme.QCoh.openComparisonComponent_not_isIso :
  ∀ (X : Scheme.{u}) (U : TopologicalSpace.Opens X.carrier) (M : Scheme.QCoh X)
    (_ : IsZero
      (((AlgebraicGeometry.Scheme.QCoh.openSectionsFunctor X U).rightDerived 1).obj M))
    (_ : ¬ IsZero
      ((AlgebraicGeometry.Scheme.QCoh.openCohomologyFunctor X U 1).obj M))
    (t : (AlgebraicGeometry.Scheme.QCoh.openSectionsFunctor X U).rightDerived 1 ⟶
      AlgebraicGeometry.Scheme.QCoh.openCohomologyFunctor X U 1),
    ¬ IsIso (t.app M))
