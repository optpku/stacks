module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number

/-!
# Intersections with effective Cartier divisors

This leaf relates the intersection number of invertible modules on a closed
subscheme to the finite-difference intersection coefficient on an effective
Cartier divisor cut out by the first module.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- If the restriction of the first invertible module to a closed subscheme is the sheaf
associated to an effective Cartier divisor, its intersection with all the factors equals the
finite-difference intersection coefficient of the restricted tail on that divisor. -/
theorem number_eq_tailPullback_of_effectiveCartierDivisor
    (k : Type u) [Field k] {d : ℕ} (hd : 0 < d)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (hZdim : topologicalKrullDim Z.subscheme = d)
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (D : Z.subscheme.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    [HasExt (Sheaf (Opens.grothendieckTopology D.subscheme.carrier) AddCommGrpCat.{u})]
    (hL₁ :
      (Scheme.Modules.pullback Z.subschemeι).obj (L ⟨0, hd⟩) ≅ D.associatedSheaf) :
    number k f Z hZdim L =
      finiteDifferenceNumber k (Z.subschemeι ≫ f) D (tailPullback hd Z L) := sorry

end AlgebraicGeometry.Scheme.Modules.Intersection
