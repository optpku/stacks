module

public import ReasLib.Algebra.Homology.DerivedCategory.NilpotentLift

/-!
# Flat module lifts versus bounded-above derived lifts

Flat liftability and bounded-above derived liftability are predicates on modules
after scalar extension.
-/

@[expose] public section

open CategoryTheory

universe u

#check (CategoryTheory.ModuleCat.NilpotentLift.existsFlatLift :
  ∀ (A' : Type u) [CommRing A'] (P' : Type u) {P : Type u}
    [CommRing P'] [CommRing P] [Algebra P' P] [Algebra A' P']
    (M : ModuleCat.{u} P), Prop)

#check (CategoryTheory.ModuleCat.NilpotentLift.existsBoundedAboveDerivedLift :
  ∀ (P' : Type u) {P : Type u}
    [CommRing P'] [CommRing P] [Algebra P' P]
    (M : ModuleCat.{u} P), Prop)

end
