/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import stacks_project.Chap103.Lemma_103_10_1_Adjunction

/-!
# Right adjoint of the inclusion of quasi-coherent modules into LQCoh^{fbc}

The inclusion `i : QCoh(𝒪_X) ⥤ LQCoh^{fbc}(𝒪_X)` on an algebraic stack has a
right adjoint `Q` with `Q ∘ i` naturally isomorphic to the identity.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Lemma 103.10.1 (1): the inclusion `QCoh.toLQCohFbc` of quasi-coherent
modules into locally quasi-coherent étale modules with the flat base change
property has a right adjoint. -/
@[stacks 0778]
instance QCoh.toLQCohFbc_isLeftAdjoint (X : GroupoidsOver S) [AlgebraicStack X] :
    (QCoh.toLQCohFbc X).IsLeftAdjoint where
  exists_rightAdjoint := ⟨LQCohFbc.toQCoh X, QCoh.toLQCohFbc_isRightAdjoint_toQCoh X⟩

/-- Lemma 103.10.1 (2): the composite of the inclusion `QCoh.toLQCohFbc` with
its right adjoint `LQCohFbc.toQCoh` is naturally isomorphic to the identity
functor on `QCoh X`. -/
@[stacks 0778]
def QCoh.toLQCohFbc_comp_toQCoh (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh.toLQCohFbc X ⋙ LQCohFbc.toQCoh X ≅ 𝟭 (QCoh X) :=
  (asIso (QCoh.toLQCohFbc_isRightAdjoint_toQCoh X).some.unit).symm

/-- The identity composite `toLQCohFbc ⋙ toQCoh ≅ 𝟭` is inverted on the nose. -/
theorem QCoh.toLQCohFbc_comp_toQCoh_hom_inv_id (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (QCoh.toLQCohFbc_comp_toQCoh X).hom ≫ (QCoh.toLQCohFbc_comp_toQCoh X).inv =
      𝟙 (QCoh.toLQCohFbc X ⋙ LQCohFbc.toQCoh X) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
