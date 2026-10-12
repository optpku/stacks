/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_2
public import stacks_project.Chap67.Definition_67_17_3_SchemeTheoreticDensity

/-!
# Intersection of scheme-theoretically dense open subspaces

The intersection of two scheme-theoretically dense open immersions of
algebraic spaces remains scheme-theoretically dense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsSchemeTheoreticallyDense

/-- Lemma 67.17.6: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `ιU` and `ιV` are scheme-theoretically dense open immersions into `X`, then
so is the inclusion `openInverseImageι ιU ιV ≫ ιU` of the open subspace
`U ∩ V` into `X`. -/
@[stacks 0837]
instance inf {S : Scheme.{u}} {X U V : AlgebraicSpace S}
    (ιU : U ⟶ X) (ιV : V ⟶ X) [IsOpenImmersion ιU] [IsOpenImmersion ιV]
    [IsSchemeTheoreticallyDense ιU] [IsSchemeTheoreticallyDense ιV] :
    IsSchemeTheoreticallyDense (openInverseImageι ιU ιV ≫ ιU) :=
  sorry

/-- Scheme-theoretic density of two open immersions implies scheme-theoretic
density of the inclusion of their intersection. -/
theorem of_inf {S : Scheme.{u}} {X U V : AlgebraicSpace S}
    {ιU : U ⟶ X} {ιV : V ⟶ X} [IsOpenImmersion ιU] [IsOpenImmersion ιV]
    (hU : IsSchemeTheoreticallyDense ιU)
    (hV : IsSchemeTheoreticallyDense ιV) :
    IsSchemeTheoreticallyDense (openInverseImageι ιU ιV ≫ ιU) :=
  sorry

end IsSchemeTheoreticallyDense

end AlgebraicGeometry.AlgebraicSpace
