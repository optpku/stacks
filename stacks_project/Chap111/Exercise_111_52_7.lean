module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.CompleteIntersection56.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.ProjectiveSpace.CompleteIntersection56

noncomputable section

universe u

/- Exercise 111.52.7 (1): if `C ⊂ P^3_k` is a type (5, 6) complete-intersection curve
with closed immersion `i`, then `χ(C, i^* O_{P^3}(n)) = 30 * n - 105` for every `n : ℤ`. -/
@[stacks 02B2]
#check (AlgebraicGeometry.ProjectiveSpace.CompleteIntersection56.eulerCharacteristic_pullbackTwistingSheaf :
  ∀ {k : Type u} [Field k]
    (F G : MvPolynomial (Fin (3 + 1)) k)
    (hF : F ∈ ProjectiveSpace.grading k 3 5)
    (hG : G ∈ ProjectiveSpace.grading k 3 6)
    (h_variety : Variety (Over.mk (hom F G hF hG)))
    (h_dim : topologicalKrullDim (scheme F G hF hG) = 1) (n : ℤ),
    Scheme.Hom.eulerCharacteristic (hom F G hF hG)
        ((Scheme.Modules.pullback (closedImmersion F G hF hG)).obj
          (twistingSheaf k 3 n)) =
      30 * n - 105)

/- Exercise 111.52.7 (2): if `C ⊂ P^3_k` is a type (5, 6) complete-intersection curve,
then `dim_k H^1(C, O_C) = 106`. -/
@[stacks 02B2]
#check (AlgebraicGeometry.ProjectiveSpace.CompleteIntersection56.cohomologyFinrank_structureSheaf_one :
  ∀ {k : Type u} [Field k]
    (F G : MvPolynomial (Fin (3 + 1)) k)
    (hF : F ∈ ProjectiveSpace.grading k 3 5)
    (hG : G ∈ ProjectiveSpace.grading k 3 6)
    (h_variety : Variety (Over.mk (hom F G hF hG)))
    (h_dim : topologicalKrullDim (scheme F G hF hG) = 1),
    Scheme.Hom.cohomologyFinrank (hom F G hF hG)
        (SheafOfModules.unit (scheme F G hF hG).ringCatSheaf : (scheme F G hF hG).Modules) 1 =
      106)
