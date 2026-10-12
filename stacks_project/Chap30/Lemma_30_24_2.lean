/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

/- Lemma 30.24.2: for a proper morphism to the spectrum of a Noetherian ring, an ample
invertible module, and a coherent formal module along the pullback of an ideal, one uniform
lower bound on twists makes the first cohomology of every transition kernel vanish. -/
@[stacks 0884] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.transitionKernel_twist_H1_eventually_isZero :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {X : Scheme.{u}}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (I : Ideal A)
      [MonoidalCategory X.Modules] (L : X.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      [AlgebraicGeometry.Scheme.Modules.IsAmple L]
      (F : AlgebraicGeometry.Scheme.CoherentFormalModules X
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec I).comap f)),
      ∃ d0 : ℤ, ∀ n : ℕ, ∀ d : ℤ, d0 ≤ d →
        IsZero (RingedSpace.moduleCohomology
          (AlgebraicGeometry.Scheme.Modules.twistByTensorPower L
            (kernel (((F.obj).stepMap n).hom)) d) 1))
