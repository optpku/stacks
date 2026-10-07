module

public import stacks_project.Chap73.Lemma_73_8_10_Cech

/-!
# Lemma 73.8.10

A property of objects of `(Spaces / X)_fppf` that is stable under Čech fibre
products of fppf covering families, and that holds on affine objects flat and
locally of finite presentation over `X`, holds on `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Fppf

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Fppf

/-- Lemma 73.8.10: let `S` be a scheme and let `X` be an algebraic space over
`S`. Let `P` be a property of objects of `(Spaces / X)_fppf`, identified with
objects of `Over X`, such that whenever `{Uᵢ ⟶ U}` is a covering in this slice
(an `FppfCovering` family of morphisms in `Over X`), if `P` holds on every
Čech fibre product `U_{i₀} ×_U ⋯ ×_U U_{iₚ}` then `P` holds on `U`. If `P`
holds for every object that is affine and flat and locally of finite
presentation over `X`, then `P` holds on `Over.mk (𝟙 X)`. -/
@[stacks 0DK6]
theorem cechEnough {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : ObjectProperty (Over X)) (h_cech : IsStableUnderCech P)
    (h_affine : ∀ (U : Over X) [IsAffine U.left] [Flat U.hom]
      [LocallyOfFinitePresentation U.hom], P U) :
    P (Over.mk (𝟙 X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Fppf
