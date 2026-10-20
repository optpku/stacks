module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Diagonal

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ChowGroup AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules

universe u

/- Lemma 42.62.5: Let `k` be a field and let `X` be an integral scheme smooth over `k`.
Let `Y`, `Z` be integral closed subschemes of `X`. Set
`d = dim Y + dim Z - dim X`. If `dim (Y ∩ Z) ≤ d` and the stalks of `Y` and of `Z`
at every point `ξ` of `Y ∩ Z` with `δ(ξ) = d` are Cohen–Macaulay, then
`[Y] · [Z] = [Y ∩ Z]_d` in `CH_d(X)`, where the product is the cap of the Chow
exterior product by the canonical Gysin class of the diagonal, of degree `dim X`,
formed from the normal sheaf of `Δ`. -/
@[stacks 0FFD] #check (AlgebraicGeometry.ChowGroup.intersectionProduct_eq_associatedCycle :
    ∀ {k : Type u} [Field k]
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
              (Scheme.IdealSheafData.inclusion (le_sup_right : Z ≤ Y ⊔ Z) ξ))),
    intersectionProduct X r D (RelativeChow.closedSubschemeClass (fun _ ↦ 0) X Y nY)
        (RelativeChow.closedSubschemeClass (fun _ ↦ 0) X Z nZ) =
      RelativeChow.closedSubschemeClass (fun _ ↦ 0) X (Y ⊔ Z) (nY + nZ - (r : ℤ)))
