module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.ProjectiveLineCover
import StacksCheckRecall

/-!
# First cohomology of a two-chart `P¹` covering

A scheme over a field covered by two opens isomorphic over the base to `P¹`, with overlap
isomorphic over the base to `A¹`, has infinite-dimensional first cohomology of `O_X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Exercise 111.63.3: Let `k` be a field and let `X` be a scheme over `k`. Assume `X` is covered
by opens `X₁` and `X₂` each isomorphic over `k` to `P¹_k`, and that `X₁ ⊓ X₂` is isomorphic over
`k` to `A¹_k`. (Such a scheme exists; for example `P¹_k` with infinity doubled.) Then
`dim_k H¹(X, O_X)` is infinite. -/
@[stacks 0G15] #check
  (AlgebraicGeometry.SchemeOverField.cohomology_one_not_finiteDimensional :
    ∀ {k : Type u} [Field k]
    (X : SchemeOverField k)
    (X₁ X₂ : X.left.Opens) (hcover : X₁ ⊔ X₂ = ⊤)
    (hX₁ : IsIsomorphic (Over.mk (X₁.ι ≫ X.hom)) (ProjectiveSpace.schemeOver k 1))
    (hX₂ : IsIsomorphic (Over.mk (X₂.ι ≫ X.hom)) (ProjectiveSpace.schemeOver k 1))
    (hX₁₂ : IsIsomorphic (Over.mk ((X₁ ⊓ X₂).ι ≫ X.hom))
      (Over.mk (𝔸(ULift.{u} (Fin 1); Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k)))),
    ¬ FiniteDimensional k
        (Scheme.Hom.cohomology X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1))
