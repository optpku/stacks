module

public import stacks_project.Chap94.Lemma_94_16_1_Groupoid
public import stacks_project.Chap100.Lemma_100_3_6_Pullback
public import stacks_project.Chap100.Lemma_100_9_8_Restrict
public import stacks_project.Chap100.Lemma_100_9_10_Substack

/-!
# Invariant subspaces cut out by a presentation

For a presentation `P : [U / R] ⟶ X` and a locally closed substack `Z ⊂ X`, the
2-fibre product `U ×_X Z` is representable by an algebraic space. Recovering the
first projection yields an immersion `U ×_X Z ⟶ U`, hence an `R`-invariant
locally closed subspace of `U`. Closed and open substacks yield closed and open
subspaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Presentation

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The algebraic space representing `U ×_X Z` for a locally closed substack `Z` of
`X`. -/
def pullbackObjectSpace (P : Presentation X) (Z : LocallyClosedSubstack X) :
    AlgebraicSpace S :=
  representingSpace
    (P.pullbackObject_isRepresentable Z.ι (inferInstance : Immersion Z.ι).representable)

/-- The recovered inclusion `U ×_X Z ⟶ U` of algebraic spaces, obtained from the
first projection of the 2-fibre product of the presentation atlas against `Z.ι`. -/
def pullbackObjectInclusion (P : Presentation X) (Z : LocallyClosedSubstack X) :
    P.pullbackObjectSpace Z ⟶ P.groupoid.U.left :=
  toGroupoids.recover
    (representingEquiv
      (P.pullbackObject_isRepresentable Z.ι (inferInstance : Immersion Z.ι).representable))
    (Bicategory.Equivalence.id _) (P.objectProjection Z.ι)

/-- The recovered inclusion `U ×_X Z ⟶ U` is an immersion of algebraic spaces. -/
instance instIsImmersion_pullbackObjectInclusion (P : Presentation X)
    (Z : LocallyClosedSubstack X) :
    AlgebraicSpace.IsImmersion (P.pullbackObjectInclusion Z) :=
  sorry

/-- The canonical `R`-invariant locally closed subspace of `U` obtained as
`U ×_X Z`. -/
def pullbackSubspace (P : Presentation X) (Z : LocallyClosedSubstack X) :
    LocallyClosedSubspace P.groupoid.U.left :=
  LocallyClosedSubspace.ofι (P.pullbackObjectInclusion Z)

/-- The inclusion of `pullbackSubspace P Z` is the recovered 2-fibre-product
projection. -/
theorem pullbackSubspace_ι (P : Presentation X) (Z : LocallyClosedSubstack X) :
    (P.pullbackSubspace Z).ι = P.pullbackObjectInclusion Z :=
  sorry

/-- The underlying algebraic space of `pullbackSubspace P Z` is
`pullbackObjectSpace P Z`. -/
theorem pullbackSubspace_X (P : Presentation X) (Z : LocallyClosedSubstack X) :
    (P.pullbackSubspace Z).X = P.pullbackObjectSpace Z :=
  sorry

/-- The locally closed subspace `U ×_X Z` is `R`-invariant. -/
theorem isLocallyClosedInvariant_pullbackSubspace (P : Presentation X)
    (Z : LocallyClosedSubstack X) :
    P.groupoid.IsLocallyClosedInvariant (P.pullbackSubspace Z) :=
  sorry

/-- The recovered inclusion `U ×_X Z ⟶ U` is a closed immersion when `Z` is a
closed substack. -/
instance instIsClosedImmersion_pullbackObjectInclusion (P : Presentation X)
    (Z : ClosedSubstack X) :
    AlgebraicSpace.IsClosedImmersion
      (P.pullbackObjectInclusion Z.toLocallyClosed) :=
  sorry

/-- The closed subspace of `U` obtained as `U ×_X Z` for a closed substack `Z`. -/
def pullbackClosedSubspace (P : Presentation X) (Z : ClosedSubstack X) :
    ClosedSubspace P.groupoid.U.left :=
  ClosedSubspace.ofι (P.pullbackObjectInclusion Z.toLocallyClosed)

/-- The inclusion of `pullbackClosedSubspace P Z` is the recovered closed
projection. -/
theorem pullbackClosedSubspace_ι (P : Presentation X) (Z : ClosedSubstack X) :
    (P.pullbackClosedSubspace Z).ι =
      P.pullbackObjectInclusion Z.toLocallyClosed :=
  sorry

/-- The locally closed inclusion of `pullbackClosedSubspace P Z` agrees with
`pullbackSubspace P Z.toLocallyClosed`. -/
theorem pullbackClosedSubspace_toLocallyClosed (P : Presentation X)
    (Z : ClosedSubstack X) :
    (P.pullbackClosedSubspace Z).toLocallyClosed.ι =
      (P.pullbackSubspace Z.toLocallyClosed).ι :=
  sorry

/-- The closed subspace `U ×_X Z` is `R`-invariant as a locally closed subspace. -/
theorem isLocallyClosedInvariant_pullbackClosedSubspace (P : Presentation X)
    (Z : ClosedSubstack X) :
    P.groupoid.IsLocallyClosedInvariant
      (P.pullbackClosedSubspace Z).toLocallyClosed :=
  sorry

/-- The recovered inclusion `U ×_X Z ⟶ U` is an open immersion when `Z` is an
open substack. -/
instance instIsOpenImmersion_pullbackObjectInclusion (P : Presentation X)
    (Z : OpenSubstack X) :
    AlgebraicSpace.IsOpenImmersion
      (P.pullbackObjectInclusion Z.toLocallyClosed) :=
  sorry

/-- The open subspace of `U` obtained as `U ×_X Z` for an open substack `Z`. -/
def pullbackOpenSubspace (P : Presentation X) (Z : OpenSubstack X) :
    OpenSubspace P.groupoid.U.left :=
  OpenSubspace.ofι (P.pullbackObjectInclusion Z.toLocallyClosed)

/-- The inclusion of `pullbackOpenSubspace P Z` is the recovered open projection. -/
theorem pullbackOpenSubspace_ι (P : Presentation X) (Z : OpenSubstack X) :
    (P.pullbackOpenSubspace Z).ι =
      P.pullbackObjectInclusion Z.toLocallyClosed :=
  sorry

/-- The locally closed inclusion of `pullbackOpenSubspace P Z` agrees with
`pullbackSubspace P Z.toLocallyClosed`. -/
theorem pullbackOpenSubspace_toLocallyClosed (P : Presentation X)
    (Z : OpenSubstack X) :
    (P.pullbackOpenSubspace Z).toLocallyClosed.ι =
      (P.pullbackSubspace Z.toLocallyClosed).ι :=
  sorry

/-- The open subspace `U ×_X Z` is open-invariant. -/
theorem isOpenInvariant_pullbackOpenSubspace (P : Presentation X)
    (Z : OpenSubstack X) :
    P.groupoid.IsOpenInvariant (P.pullbackOpenSubspace Z) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Presentation
