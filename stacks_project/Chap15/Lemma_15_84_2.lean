module
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect
import Mathlib.RingTheory.FinitePresentation
import StacksCheckRecall

/-!
# Lemma 15.84.2

@stack 0DHT
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.84.2 (1), tag `0DHT`: relative-perfect objects form a strictly full
subcategory. -/
@[stacks 0DHT "(1), strictly full"]
#check fun {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K L : DerivedCategory (ModuleCat A)} (hK : K.IsPerfectOver R) (e : K ≅ L) =>
  (hK.ofIso e : L.IsPerfectOver R)

/- Lemma 15.84.2 (2), tag `0DHT`: relative-perfect objects form a triangulated
subcategory. -/
@[stacks 0DHT "(2), triangulated"]
#check fun (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A] =>
  (DerivedCategory.perfectOver_isTriangulated R A :
    (DerivedCategory.perfectOver R A).IsTriangulated)

/- Lemma 15.84.2 (3), tag `0DHT`: relative-perfect objects form a saturated
subcategory. -/
@[stacks 0DHT "(3), saturated"]
#check fun (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A] =>
  (DerivedCategory.perfectOver_isStableUnderRetracts R A :
    (DerivedCategory.perfectOver R A).IsStableUnderRetracts)

end
