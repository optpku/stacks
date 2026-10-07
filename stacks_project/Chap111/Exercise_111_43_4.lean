module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211.Cohomology
import StacksCheckRecall

/-!
# Exercise 111.43.4

An explicit type (2, 11) complete-intersection curve in `P^3_k` which is
projective of dimension 1 over a field `k`, with canonical identification
`Γ(X, 𝒪_X) = k` and `dim_k H¹(X, 𝒪_X) = 100`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Exercise 111.43.4 (1): the explicit complete-intersection curve is projective
over the field `k`. -/
@[stacks 0DAM] #check
  (AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211.instProjective_hom :
    ∀ (k : Type u) [Field k],
      Projective (AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211.hom k))

/- Exercise 111.43.4 (2): the explicit complete-intersection curve has dimension
one. -/
@[stacks 0DAM] #check
  (AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211.topologicalKrullDim_eq_one :
    ∀ (k : Type u) [Field k],
      topologicalKrullDim
          (AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211.scheme k) = 1)

/- Exercise 111.43.4 (3): the canonical map `k → Γ(X, 𝒪_X)` is bijective. -/
@[stacks 0DAM] #check
  (AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211.globalSectionsMap_bijective :
    ∀ (k : Type u) [Field k],
      Function.Bijective
        (AlgebraicGeometry.Scheme.Hom.globalSectionsMap
          (AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211.hom k)))

/- Exercise 111.43.4 (4): `dim_k H¹(X, 𝒪_X) = 100`. -/
@[stacks 0DAM] #check
  (AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211.cohomologyFinrank_structureSheaf_one :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.Scheme.Hom.cohomologyFinrank
          (AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211.hom k)
          (SheafOfModules.unit
            (AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211.scheme k).ringCatSheaf :
            (AlgebraicGeometry.ProjectiveSpace.CompleteIntersection211.scheme k).Modules) 1 =
        100)

end
