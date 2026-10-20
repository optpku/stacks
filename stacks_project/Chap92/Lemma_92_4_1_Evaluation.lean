module

public import ReasLib.AlgebraicTopology.SimplicialObject.PolynomialAugmentation

/-!
# Cosimplicial evaluation on polynomial augmentations

The shared augmentation owner constructs the cosimplicial polynomial-site object.
-/

@[expose] public section

open CategoryTheory Algebra

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {P : SimplicialObject (CommAlgCat.{u} A)}
variable (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))
variable (hP : ∀ n, IsPolynomial A (P.obj n))

#check (Algebra.PolynomialSite.asCosimplicial ε hP : CosimplicialObject (PolynomialSite A B))
