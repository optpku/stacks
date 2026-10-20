module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Noetherian
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

/- Lemma 64.12.2. Let `R` be a left Noetherian ring and `K` an object of
`D(R)`. Then `K` is perfect if and only if it has finite Tor-dimension and,
for every `i : ℤ`, the cohomology module `H^i(K)` is a finite left `R`-module.

Stacks states the lemma for a possibly noncommutative left Noetherian ring.
The Lean statement is the commutative specialization supported by
`HasFiniteTorDimension`, whose module-category API requires `[CommRing R]`.
The assumption `[IsNoetherianRing R]` records left-Noetherianity. Finite
Tor-dimension already forces `K` to lie in `Dᵇ(R)`. -/
@[stacks 03TO] #check
  (CategoryTheory.DerivedCategory.isPerfect_iff_hasFiniteTorDimension_and_finite_homology :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (K : DerivedCategory (ModuleCat R)),
      K.IsPerfect ↔
        HasFiniteTorDimension R K ∧
          ∀ i : ℤ, Module.Finite R
            ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K))

#check (CategoryTheory.DerivedCategory.IsPerfect.homology_finite :
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] {K : DerivedCategory (ModuleCat R)},
    K.IsPerfect → ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K))

#check (CategoryTheory.DerivedCategory.isPerfect_of_hasFiniteTorDimension_of_finite_homology :
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] {K : DerivedCategory (ModuleCat R)},
    HasFiniteTorDimension R K →
      (∀ i : ℤ, Module.Finite R
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K)) → K.IsPerfect)

end CategoryTheory.DerivedCategory
