module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Grothendieck
import StacksCheckRecall

/-!
# Lemma 15.87.9

@stack 07KX
-/

@[expose] public section

/- Lemma 15.87.9: the total right derived inverse limit of an object of the derived category of
sequential inverse systems of abelian groups admits derived-limit data for its stagewise tower.
The data are noncanonical, so the shared statement correctly records their nonemptiness rather
than choosing a derived-limit presentation. -/
@[stacks 07KX] #check @CategoryTheory.DerivedLimit.isDerivedLimit_of_tower
