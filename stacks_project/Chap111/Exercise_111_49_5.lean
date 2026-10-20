module

public import ReasLib.AlgebraicGeometry.QuadricCone
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.QuadricCone CategoryTheory

universe u

/- Exercise 111.49.5: the ruling Weil divisor on the quadratic cone
`Spec (k[X₀, X₁, X₂] / (X₀ * X₁ - X₂ ^ 2))` is not the Weil divisor associated
to any Cartier divisor. -/
@[stacks 02F8] #check (AlgebraicGeometry.QuadricCone.ruling_not_mem_range_weilDivisor_ofCartier :
  ∀ (k : Type u) [Field k]
    [HasSheafify (Opens.grothendieckTopology (scheme k).toTopCat) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (scheme k).toTopCat).HasSheafCompose
      (forget CommRingCat.{u})],
    rulingWeilDivisor k ∉ Set.range
      (weilDivisor_ofCartier : CartierDivisor (scheme k) → WeilDivisor (scheme k)))
