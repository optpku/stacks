/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Koszul.PrincipalOpen
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul
open KoszulComplex.PowerTower

universe u

/- 36.9.4.1: For the powered Koszul ideal system `Iₑ` determined by `f`, the
canonical restriction maps `Hom(Iₑ, E) ⟶ H⁰(U, E)` induce
`colimₑ Hom(Iₑ, E) ⟶ H⁰(U, E)`, where `X = Spec(A)` and
`U = AlgebraicGeometry.Scheme.PrincipalOpenCech.openSubset f`. -/
@[stacks 08DC]
#check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul.homColimitToOpenH0 :
    ∀ {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived
        (Spec (CommRingCat.of A)).toRingedSpace),
      colimit (homDiagram (derivedIdealSystem f ⋙ affineDerivedTilde A) E) ⟶
        restrictionHomH0 f E)
