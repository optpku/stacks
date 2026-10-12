/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap73.Definition_73_8_1_PhCovering
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 73.8.1: Let `S` be a scheme and let `X` be an algebraic space over
`S`. A ph covering of `X` is a family of morphisms `{fᵢ : Xᵢ ⟶ X}` of algebraic
spaces over `S` that are locally of finite type, such that every morphism from
an affine scheme `U` to `X` admits a standard ph covering of `U` refining the
family `{Xᵢ ×_X U ⟶ U}`. -/
@[stacks 0DFG] #check AlgebraicGeometry.AlgebraicSpace.PhCovering

#check AlgebraicGeometry.AlgebraicSpace.PhCovering.source_spec
#check AlgebraicGeometry.AlgebraicSpace.PhCovering.exists_indices
#check AlgebraicGeometry.AlgebraicSpace.phCovering_ofOver_iff
