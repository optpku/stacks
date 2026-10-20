module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothGroupoid
public import ReasLib.AlgebraicGeometry.FormalDeformation.SchlessingerH4
public import ReasLib.CategoryTheory.Groupoid.Quotient

/-!
# Rim-Schlessinger for quotients of smooth groupoids in functors

The quotient of a smooth groupoid in functors satisfies the Rim-Schlessinger
condition when its object and arrow functors satisfy Schlessinger's (H4).
-/

@[expose] public section

open CategoryTheory

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- The quotient of a smooth groupoid in functors on `ArtinianLocalAlgCat Λ k`
satisfies the Rim-Schlessinger condition if its object and arrow functors satisfy
Schlessinger's (H4). -/
@[stacks 06KT]
theorem hasRimSchlessinger_quotient
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] (hU : Functor.HasSchlessingerH4 G.U)
    (hR : Functor.HasSchlessingerH4 G.R) :
    Functor.HasRimSchlessinger G.quotient.p := sorry

end CategoryTheory.GroupoidInFunctors
