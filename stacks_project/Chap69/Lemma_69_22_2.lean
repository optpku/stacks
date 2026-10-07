module

public import stacks_project.Chap69.Lemma_69_22_2_Cohomology
public import stacks_project.Chap69.Lemma_69_22_2_IdealPower
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.22.2: in Situation 69.22.1, set B = ⨁_{n ≥ 0} I^n. Then for every
p ≥ 0 the graded B-module ⨁_{n ≥ 0} H^p(X, I^n F) is a finite B-module. Here
B is reesAlgebra I and the graded module is carrier with the explicit action
module. -/
@[stacks 08AW] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.finite :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [IsNoetherianRing A]
      (I : Ideal A)
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
      (F : X.Modules) [F.IsCoherent]
      [Abelian X.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
      [HasInjectiveResolutions X.Modules]
      (p : ℕ),
      Module.FiniteWithAction (reesAlgebra I)
        (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.carrier I f F p)
        (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.module I f F p))
