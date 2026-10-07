module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.CompleteIntersection56
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.CompleteIntersection56

/-- Euler characteristic of `i^* O(n)` on a type (5, 6) complete-intersection curve equals
the alternating combination of Euler characteristics of `O(n)`, `O(n - 5)`, `O(n - 6)`,
and `O(n - 11)` on `P^3_k`. -/
theorem eulerCharacteristic_eq_alternatingTwists {k : Type u} [Field k]
    (F G : MvPolynomial (Fin (3 + 1)) k)
    (hF : F ∈ ProjectiveSpace.grading k 3 5)
    (hG : G ∈ ProjectiveSpace.grading k 3 6)
    (h_variety : Variety (Over.mk (hom F G hF hG)))
    (h_dim : topologicalKrullDim (scheme F G hF hG) = 1) (n : ℤ) :
    Scheme.Hom.eulerCharacteristic (hom F G hF hG)
        ((Scheme.Modules.pullback (closedImmersion F G hF hG)).obj
          (twistingSheaf k 3 n)) =
      Scheme.Hom.eulerCharacteristic (toSpec k 3) (twistingSheaf k 3 n) -
        Scheme.Hom.eulerCharacteristic (toSpec k 3) (twistingSheaf k 3 (n - 5)) -
          Scheme.Hom.eulerCharacteristic (toSpec k 3) (twistingSheaf k 3 (n - 6)) +
            Scheme.Hom.eulerCharacteristic (toSpec k 3) (twistingSheaf k 3 (n - 11)) := sorry

/-- For a type (5, 6) complete-intersection curve with closed immersion `i` into `P^3_k`,
the Euler characteristic of `i^* O(n)` is `30 * n - 105` for every integer `n`. -/
theorem eulerCharacteristic_pullbackTwistingSheaf {k : Type u} [Field k]
    (F G : MvPolynomial (Fin (3 + 1)) k)
    (hF : F ∈ ProjectiveSpace.grading k 3 5)
    (hG : G ∈ ProjectiveSpace.grading k 3 6)
    (h_variety : Variety (Over.mk (hom F G hF hG)))
    (h_dim : topologicalKrullDim (scheme F G hF hG) = 1) (n : ℤ) :
    Scheme.Hom.eulerCharacteristic (hom F G hF hG)
        ((Scheme.Modules.pullback (closedImmersion F G hF hG)).obj
          (twistingSheaf k 3 n)) =
      30 * n - 105 := sorry

/-- The first cohomology of the structure sheaf of a type (5, 6) complete-intersection
curve in `P^3_k` has dimension `106` over `k`. -/
theorem cohomologyFinrank_structureSheaf_one {k : Type u} [Field k]
    (F G : MvPolynomial (Fin (3 + 1)) k)
    (hF : F ∈ ProjectiveSpace.grading k 3 5)
    (hG : G ∈ ProjectiveSpace.grading k 3 6)
    (h_variety : Variety (Over.mk (hom F G hF hG)))
    (h_dim : topologicalKrullDim (scheme F G hF hG) = 1) :
    Scheme.Hom.cohomologyFinrank (hom F G hF hG)
        (SheafOfModules.unit (scheme F G hF hG).ringCatSheaf : (scheme F G hF hG).Modules) 1 =
      106 := sorry

end AlgebraicGeometry.ProjectiveSpace.CompleteIntersection56
