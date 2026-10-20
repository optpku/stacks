module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Quotient

/-!
# Dual-number orbit quotients

The orbit quotient functor, its category-of-elements projection, its based quotient
map, and its explicit formal tower are provided by the shared mathematical owner.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (G : Subgroup (Aut (dualNumber Λ k)))

/- Example 90.15.3: the dual-number represented functor modulo the supplied
residue-compatible automorphism subgroup. -/
#check (ArtinianLocalAlgCat.quotientBy G : ArtinianLocalAlgCat Λ k ⥤ Type u)

#check (ArtinianLocalAlgCat.quotientProjection G :
  quotientTotal G ⥤ ArtinianLocalAlgCat Λ k)

#check (ArtinianLocalAlgCat.quotientBasedFunctor G :
  BasedCategory.ofFunctor
      (CompleteLocalAlgCat.identityProjection (dualNumberComplete Λ k)) ⥤ᵇ
    BasedCategory.ofFunctor (quotientProjection G))

#check (ArtinianLocalAlgCat.quotientFormalObject G : FormalObject (quotientProjection G))
