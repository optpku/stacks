module

public import stacks_project.Chap99.Lemma_99_5_3_Isom

/-!
# Lemma 99.5.3

In Situation 99.5.1 the diagonal of the stack of coherent sheaves is
representable by algebraic spaces, in the sense of Algebraic Stacks,
Lemma 94.10.11 (1): fibrewise Isom presheaves are algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.5.3: in Situation 99.5.1, with `𝒳 = CohStack f`, the diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces. At Hom-universe `u + 1`
this is the 94.10.11(1) condition that for every scheme `T` over `S` and
objects `x, y` of the fibre `𝒳_T`, the presheaf `Isom_𝒳(x, y)` is an algebraic
space over `T`. -/
@[stacks 08W6]
theorem isom_isAlgebraicSpace (f : X ⟶ B) [FinitePresentation f]
    [Functor.IsFibered (p f)] : isAlgebraicSpace f := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
