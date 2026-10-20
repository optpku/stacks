/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap94.Definition_94_16_5_Presentation
public import stacks_project.Chap100.Lemma_100_9_8_QuotientMap
public import stacks_project.Chap100.Lemma_100_9_10_Substack

/-!
# Substacks from invariant subspaces of a presentation

An `R`-invariant locally closed subspace `Z ⊂ U` of a presentation
`P : [U / R] ⟶ X` determines a locally closed substack of `X` as the strictly
full image of `[Z / R_Z] ⟶ X`. Closed and open invariant subspaces yield closed
and open substacks. A morphism of algebraic stacks factors through a substack
when it is 2-isomorphic to a composite through the inclusion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

variable {S : Scheme.{u}}

/-- A 1-morphism `f : Y ⟶ X` factors through `ι : Z ⟶ X` when there is a
1-morphism `g : Y ⟶ Z` together with a 2-isomorphism `g ≫ ι ≅ f`. -/
def FactorsThrough {X Y Z : GroupoidsOver S} (f : Y ⟶ X) (ι : Z ⟶ X) : Prop :=
  ∃ g : Y ⟶ Z, Nonempty (g ≫ ι ≅ f)

/-- Factoring through a 1-morphism unfolds to a 2-isomorphic factorization. -/
theorem factorsThrough_iff {X Y Z : GroupoidsOver S} (f : Y ⟶ X) (ι : Z ⟶ X) :
    FactorsThrough f ι ↔ ∃ g : Y ⟶ Z, Nonempty (g ≫ ι ≅ f) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom

namespace AlgebraicGeometry.AlgebraicStack.Presentation

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The morphism `[Z / R_Z] ⟶ X` obtained by composing the restricted quotient
map with the presenting equivalence. -/
abbrev restrictQuotientToX (P : Presentation X)
    (Z : LocallyClosedSubspace P.groupoid.U.left) :
    (GroupoidAlgebraicSpace.restrict P.groupoid Z).quotientStack ⟶ X :=
  GroupoidAlgebraicSpace.restrictQuotientHom P.groupoid Z ≫ P.hom

/-- `restrictQuotientToX` is the composite of `restrictQuotientHom` with `P.hom`. -/
theorem restrictQuotientToX_eq (P : Presentation X)
    (Z : LocallyClosedSubspace P.groupoid.U.left) :
    P.restrictQuotientToX Z =
      GroupoidAlgebraicSpace.restrictQuotientHom P.groupoid Z ≫ P.hom :=
  sorry

/-- The composite `[Z / R_Z] ⟶ X` is an immersion when `Z ⊂ U` is `R`-invariant. -/
theorem immersion_restrictQuotientHom_comp_hom (P : Presentation X)
    (Z : LocallyClosedSubspace P.groupoid.U.left)
    (hZ : P.groupoid.IsLocallyClosedInvariant Z) :
    Immersion (P.restrictQuotientToX Z) :=
  sorry

/-- The composite `[Z / R_Z] ⟶ X` is a closed immersion when `Z ⊂ U` is a closed
`R`-invariant subspace. -/
theorem closedImmersion_restrictQuotientHom_comp_hom (P : Presentation X)
    (C : ClosedSubspace P.groupoid.U.left)
    (hC : P.groupoid.IsLocallyClosedInvariant C.toLocallyClosed) :
    ClosedImmersion (P.restrictQuotientToX C.toLocallyClosed) :=
  sorry

/-- The composite `[Z / R_Z] ⟶ X` is an open immersion when `Z ⊂ U` is an open
`R`-invariant subspace. -/
theorem openImmersion_restrictQuotientHom_comp_hom (P : Presentation X)
    (W : OpenSubspace P.groupoid.U.left) (hW : P.groupoid.IsOpenInvariant W) :
    OpenImmersion (P.restrictQuotientToX W.toLocallyClosed) :=
  sorry

/-- The locally closed substack of `X` associated to an `R`-invariant locally
closed subspace of `U`, as the strictly full image of `[Z / R_Z] ⟶ X`. -/
def ofInvariantSubspace (P : Presentation X)
    (Z : LocallyClosedSubspace P.groupoid.U.left)
    (hZ : P.groupoid.IsLocallyClosedInvariant Z) :
    LocallyClosedSubstack X where
  Y := ofFunctor ((LocallyClosedSubstack.imageObjects (P.restrictQuotientToX Z)).ι ⋙ X.p)
  ι := inclusionOf X (LocallyClosedSubstack.imageObjects (P.restrictQuotientToX Z))
  isAlgebraicStack := sorry
  isImmersion := sorry
  isStrictlyFull := sorry

/-- The objects of `ofInvariantSubspace P Z hZ` are the essential image of
`[Z / R_Z] ⟶ X`. -/
theorem ofInvariantSubspace_objectProperty_def (P : Presentation X)
    (Z : LocallyClosedSubspace P.groupoid.U.left)
    (hZ : P.groupoid.IsLocallyClosedInvariant Z) :
    (P.ofInvariantSubspace Z hZ).objectProperty =
      LocallyClosedSubstack.imageObjects (P.restrictQuotientToX Z) :=
  sorry

/-- The closed substack of `X` associated to an `R`-invariant closed subspace of
`U`, as the strictly full image of `[Z / R_Z] ⟶ X`. -/
def ofInvariantClosedSubspace (P : Presentation X)
    (C : ClosedSubspace P.groupoid.U.left)
    (hC : P.groupoid.IsLocallyClosedInvariant C.toLocallyClosed) :
    ClosedSubstack X where
  Y := ofFunctor
    ((LocallyClosedSubstack.imageObjects (P.restrictQuotientToX C.toLocallyClosed)).ι ⋙
      X.p)
  ι := inclusionOf X
    (LocallyClosedSubstack.imageObjects (P.restrictQuotientToX C.toLocallyClosed))
  isAlgebraicStack := sorry
  isClosedImmersion := sorry
  isStrictlyFull := sorry

/-- The objects of `ofInvariantClosedSubspace P C hC` are the essential image of
`[Z / R_Z] ⟶ X`. -/
theorem ofInvariantClosedSubspace_objectProperty_def (P : Presentation X)
    (C : ClosedSubspace P.groupoid.U.left)
    (hC : P.groupoid.IsLocallyClosedInvariant C.toLocallyClosed) :
    (P.ofInvariantClosedSubspace C hC).objectProperty =
      LocallyClosedSubstack.imageObjects (P.restrictQuotientToX C.toLocallyClosed) :=
  sorry

/-- The open substack of `X` associated to an `R`-invariant open subspace of `U`,
as the strictly full image of `[Z / R_Z] ⟶ X`. -/
def ofInvariantOpenSubspace (P : Presentation X)
    (W : OpenSubspace P.groupoid.U.left) (hW : P.groupoid.IsOpenInvariant W) :
    OpenSubstack X where
  Y := ofFunctor
    ((LocallyClosedSubstack.imageObjects (P.restrictQuotientToX W.toLocallyClosed)).ι ⋙
      X.p)
  ι := inclusionOf X
    (LocallyClosedSubstack.imageObjects (P.restrictQuotientToX W.toLocallyClosed))
  isAlgebraicStack := sorry
  isOpenImmersion := sorry
  isStrictlyFull := sorry

/-- The objects of `ofInvariantOpenSubspace P W hW` are the essential image of
`[Z / R_Z] ⟶ X`. -/
theorem ofInvariantOpenSubspace_objectProperty_def (P : Presentation X)
    (W : OpenSubspace P.groupoid.U.left) (hW : P.groupoid.IsOpenInvariant W) :
    (P.ofInvariantOpenSubspace W hW).objectProperty =
      LocallyClosedSubstack.imageObjects (P.restrictQuotientToX W.toLocallyClosed) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Presentation
