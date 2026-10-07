module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.SmallAcyclic
public import ReasLib.Algebra.Homology.CochainComplex.SmallAcyclic.Grothendieck
import StacksCheckRecall

@[expose] public section

/-!
# Detecting K-Injective Complexes on Small Acyclic Sources

The reusable test-family vanishing predicate, its orthogonality bridge, and the K-injectivity
criterion are owned by ReasLib. This file records the Grothendieck-category source statement as
a typed check.
-/

open CategoryTheory
open ComplexShape

universe w v u

namespace CochainComplex

/- Lemma 19.12.3: for a cardinal satisfying both conclusions of Lemma 19.12.2, a termwise
injective complex is K-injective if maps to it from all bounded-above acyclic complexes
controlled by that cardinal vanish in the homotopy category. -/
@[stacks 079L] #check
  fun (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
      (kappa : Cardinal.{max u v + 1})
      (hbound : SmallAcyclic.IsUniformBound A kappa)
      (I : CochainComplex A ℤ) [∀ j : ℤ, Injective (I.X j)]
      (hvanish : SmallAcyclic.HomotopyVanishing kappa I) ↦
    (IsKInjective.ofSmallAcyclic I kappa hbound.hasSubcomplexes hvanish : I.IsKInjective)

#check @SmallAcyclic.HomotopyVanishing
#check @SmallAcyclic.HomotopyVanishing.rightOrthogonal
#check @IsKInjective.ofSmallAcyclic

end CochainComplex
