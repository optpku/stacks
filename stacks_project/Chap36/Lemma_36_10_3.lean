module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Noetherian
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
public import stacks_project.Chap36.Lemma_36_10_1_PseudoCoherent

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

/- Lemma 36.10.3 (1): over a Noetherian scheme, an object of `D_QCoh(𝒪_X)` is
`m`-pseudo-coherent exactly when it is bounded above and its cohomology sheaves in degrees
`i ≥ m` are coherent. -/
@[stacks 08E8] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isMPseudoCoherent_iff_boundedAbove_and_cohomology_coherent_ge :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (E : Scheme.DerivedQCoh X) (m : ℤ),
      Scheme.IsMPseudoCoherent X E.obj m ↔
        (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ∧
          ∀ i : ℤ, m ≤ i →
            (RingedSpace.ModuleDerived.cohomologySheaf E.obj i).IsCoherent)

/- Lemma 36.10.3 (2): over a Noetherian scheme, an object of `D_QCoh(𝒪_X)` is
pseudo-coherent exactly when it is bounded above and has coherent cohomology in every degree. -/
@[stacks 08E8] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isPseudoCoherent_iff_boundedAbove_and_cohomology_coherent :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (E : Scheme.DerivedQCoh X),
      Scheme.IsPseudoCoherent X E.obj ↔
        (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ∧
          DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E.obj)
