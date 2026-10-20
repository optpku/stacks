module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Cartier.Weil

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Scheme

/-- There exists a Weil divisor on a variety that is not associated to any Cartier divisor,
but whose multiple by some natural number greater than one is associated to a Cartier divisor. -/
@[stacks 02F9]
theorem exists_weilDivisor_nsmul_ofCartier_not_ofCartier :
    ∃ (k : Type u) (_ : Field k) (X : SchemeOverField k) (_ : Variety X)
      (_ : IsNoetherian X.left)
      (_ : HasSheafify (Opens.grothendieckTopology X.left.toTopCat) AddCommGrpCat.{u})
      (_ : (Opens.grothendieckTopology X.left.toTopCat).HasSheafCompose
        (forget CommRingCat.{u}))
      (D : WeilDivisor X.left) (n : ℕ),
      1 < n ∧
        (∀ τ : CartierDivisor X.left, weilDivisor_ofCartier τ ≠ D) ∧
          ∃ τ : CartierDivisor X.left, weilDivisor_ofCartier τ = n • D :=
  sorry

end AlgebraicGeometry
