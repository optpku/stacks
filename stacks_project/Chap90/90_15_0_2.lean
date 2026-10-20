module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Orbits

/-!
# Bijective differential on Derivation Λ k k-orbits

The named condition of Stacks Tag 06T6 is orbit bijectivity of the differential
associated to a formal object of a predeformation category.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- 90.15.0.2: the differential of a formal object is bijective on
`Derivation Λ k k`-orbits. This names a condition on the formal object. -/
@[stacks 06T6] #check (FormalObject.BijectiveDifferentialOnOrbits :
  (ξ : FormalObject p) → [Functor.IsPredeformationCategory p] → Prop)
