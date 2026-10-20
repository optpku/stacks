/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PrincipalCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SequentialInverseSystem
open CategoryTheory.End.Power CategoryTheory.Linear.PrincipalPower
open CategoryTheory.DerivedCategory.PrincipalPower.CohomologyDiagram
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.FlatPullbackSections

noncomputable section

universe u

/- Lemma 52.3.2 (1): derived sections of the principal-power quotient limit
are identified with principal derived completion. -/
@[stacks 0BLD] #check
  (AlgebraicGeometry.Scheme.PrincipalCompletion.derivedSectionsLimit_isomorphic_derivedCompletion :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
      (g : X ⟶ Spec (CommRingCat.of A)) (f : A) (F : X.Modules) [F.IsQuasicoherent]
      (hstable : kernelStabilizes
        (RingedSpace.globalSectionMul (Scheme.Hom.globalSectionsMap g f)
          ((Scheme.Modules.toRingedSpace X).obj F))),
      IsIsomorphic
        ((AlgebraicGeometry.Scheme.FlatPullbackSections.baseSections g).obj
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
            (limit (quotientSystem
              (Scheme.Hom.globalSectionsMap g f)
              ((Scheme.Modules.toRingedSpace X).obj F)))))
        (DerivedCategory.derivedCompletionOf (principalIdeal f) (principalIdeal_fg f)
          ((AlgebraicGeometry.Scheme.FlatPullbackSections.baseSections g).obj
            ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
              ((Scheme.Modules.toRingedSpace X).obj F)))))

/- Lemma 52.3.2 (2): the cohomology and completion terms form the displayed
commutative diagram in every degree. -/
@[stacks 0BLD] #check
  (AlgebraicGeometry.Scheme.PrincipalCompletion.existsCohomologyDiagram :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
      (g : X ⟶ Spec (CommRingCat.of A)) (f : A) (F : X.Modules) [F.IsQuasicoherent]
      (hstable : kernelStabilizes
        (RingedSpace.globalSectionMul (Scheme.Hom.globalSectionsMap g f)
          ((Scheme.Modules.toRingedSpace X).obj F))) (p : ℤ),
      Nonempty (AlgebraicGeometry.Scheme.PrincipalCompletion.CohomologyDiagram g f F p))
