/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Presentation

/-! # Chosen smooth presentations of algebraic stacks -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace AlgebraicStack

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The scheme over the base selected from the smooth surjective atlas axiom. -/
def algebraicStackAtlasOver (X : GroupoidsOver S) [AlgebraicStack X] : Over S :=
  (inferInstance : AlgebraicStack X).existsSmoothSurjectiveAtlas.choose

/-- The morphism from the selected scheme atlas to the algebraic stack. -/
def algebraicStackAtlasHom (X : GroupoidsOver S) [AlgebraicStack X] :
    GroupoidsOver.slice (algebraicStackAtlasOver X) ⟶ X :=
  (inferInstance : AlgebraicStack X).existsSmoothSurjectiveAtlas.choose_spec.choose

/-- The selected atlas morphism is smooth and surjective. -/
theorem algebraicStackAtlas_spec (X : GroupoidsOver S) [AlgebraicStack X] :
    Groupoids.Hom.Smooth (algebraicStackAtlasHom X) ∧
      Groupoids.Hom.Surjective (algebraicStackAtlasHom X) := sorry

/-- The selected atlas morphism is smooth. -/
theorem algebraicStackAtlasHom.smooth (X : GroupoidsOver S) [AlgebraicStack X] :
    Groupoids.Hom.Smooth (algebraicStackAtlasHom X) :=
  (inferInstance : AlgebraicStack X).existsSmoothSurjectiveAtlas.choose_spec.choose_spec.1

/-- The selected atlas morphism is surjective. -/
theorem algebraicStackAtlasHom.surjective (X : GroupoidsOver S) [AlgebraicStack X] :
    Groupoids.Hom.Surjective (algebraicStackAtlasHom X) :=
  (inferInstance : AlgebraicStack X).existsSmoothSurjectiveAtlas.choose_spec.choose_spec.2

/-- The slice fibration of a scheme is represented by its associated algebraic space. -/
theorem sliceRepresentable (U : Over S) :
    IsRepresentableByAlgebraicSpace (GroupoidsOver.slice U) :=
  ⟨ofOver U, ⟨(ofOverSliceEquiv U).symm⟩⟩

/-- The kernel pair of the selected smooth atlas gives a smooth presentation
of an algebraic stack. -/
def algebraicStackPresentation (X : GroupoidsOver S) [AlgebraicStack X] :
    Presentation X :=
  @Presentation.ofSmoothSurjective S X _ (algebraicStackAtlasHom X) inferInstance
    (sliceRepresentable (algebraicStackAtlasOver X))
    (algebraicStackAtlasHom.smooth X) (algebraicStackAtlasHom.surjective X)

end AlgebraicGeometry.GroupoidsOver
