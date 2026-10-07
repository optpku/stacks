module

public import stacks_project.Chap42.Lemma_42_62_5_IntersectionProduct
public import ReasLib.RingTheory.CohenMacaulay.Ring
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k]

/-- Lemma 42.62.5: Let `k` be a field and let `X` be an integral scheme smooth over `k`.
Let `Y`, `Z` be integral closed subschemes of `X`. Set
`d = dim Y + dim Z - dim X`. If `dim (Y ∩ Z) ≤ d` and the stalks of `Y` and of `Z`
at every point `ξ` of `Y ∩ Z` with `δ(ξ) = d` are Cohen–Macaulay, then
`[Y] · [Z] = [Y ∩ Z]_d` in `CH_d(X)`, where the product is the cap of the Chow
exterior product by the canonical Gysin class of the diagonal, of degree `dim X`,
formed from the normal sheaf of `Δ`. -/
@[stacks 0FFD]
theorem intersectionProduct_eq_associatedCycle
    (X : SchemeOverField k) [IsIntegral X.left] [Smooth X.hom]
    (Y Z : X.left.IdealSheafData)
    [IsIntegral Y.subscheme] [IsIntegral Z.subscheme]
    {nX nY nZ : ℤ} {r : ℕ}
    (hnX : nX = X.hom.relativeDimensionFunction (fun _ ↦ 0) (genericPoint X.left))
    (hnY : nY = X.hom.relativeDimensionFunction (fun _ ↦ 0)
      (Y.subschemeι (genericPoint Y.subscheme)))
    (hnZ : nZ = X.hom.relativeDimensionFunction (fun _ ↦ 0)
      (Z.subschemeι (genericPoint Z.subscheme)))
    (hr : nX = r)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (hY : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) Y ≤ (nY : EInt))
    (hZ : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) Z ≤ (nZ : EInt))
    (h_dim : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) (Y ⊔ Z) ≤
      (nY + nZ - (r : ℤ) : EInt))
    (h_CM : ∀ ξ : (Y ⊔ Z).subscheme,
      X.hom.relativeDimensionFunction (fun _ ↦ 0) ((Y ⊔ Z).subschemeι ξ) =
          nY + nZ - nX →
        CohenMacaulayRing
            (Y.subscheme.presheaf.stalk
              (Scheme.IdealSheafData.inclusion (le_sup_left : Y ≤ Y ⊔ Z) ξ)) ∧
          CohenMacaulayRing
            (Z.subscheme.presheaf.stalk
              (Scheme.IdealSheafData.inclusion (le_sup_right : Z ≤ Y ⊔ Z) ξ))) :
    intersectionProduct X r D (closedSubschemeClass X Y nY hY)
        (closedSubschemeClass X Z nZ hZ) =
      closedSubschemeClass X (Y ⊔ Z) (nY + nZ - (r : ℤ)) h_dim := sorry

end AlgebraicGeometry.ChowGroup
