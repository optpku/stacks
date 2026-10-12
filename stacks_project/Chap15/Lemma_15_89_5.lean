/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.IdealPower.Serre
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.89.5

@stack 0A6K
-/

open CategoryTheory

universe u v

section

variable {R : Type u} [CommRing R]

/- Lemma 15.89.5 (Stacks 0A6K): the object property of `I`-power torsion modules is a
Serre class in `ModuleCat R`. -/
@[stacks 0A6K]
#check fun (I : Ideal R) ↦
  (CategoryTheory.ModuleCat.isIdealPowerTorsion_isSerreClass I :
    (CategoryTheory.ModuleCat.isIdealPowerTorsion I :
      ObjectProperty (ModuleCat.{v} R)).IsSerreClass)

#check fun (I : Ideal R) ↦
  (CategoryTheory.ModuleCat.isIdealPowerTorsion I :
    ObjectProperty (ModuleCat.{v} R))

end
