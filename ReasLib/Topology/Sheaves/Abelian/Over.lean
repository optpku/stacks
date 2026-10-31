/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Topology.Sheaves.Over
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

/-!
# Abelian sheafification on slices of an opens site

The opens site of a topological space and its first two slice levels have the standard
`AddCommGrpCat` sheafification and local-bijectivity instances.  These are topology facts, so
they do not depend on a chosen ring sheaf. The coefficient universe contains the space
universe, as in the canonical sheafification on the unsliced opens site.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace

noncomputable section

universe u w

namespace TopCat

/-- Transport the existing sheafification on the open subspace along the canonical
equivalence between its opens and the slice site. -/
private theorem addCommGrpHasSheafifyOver (X : TopCat.{u}) (U : Opens X) :
    HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{max u w} := by
  letI := addCommGrpHasSheafify.{w, u} (TopCat.of U)
  exact Equivalence.hasSheafify ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology U) U.overEquivalence AddCommGrpCat.{max u w}

/-- Abelian-group-valued weak sheafification is available on every slice of an opens site,
with coefficients in a universe containing the space. -/
instance addCommGrpHasWeakSheafifyOver (X : TopCat.{u}) :
    ∀ U : Opens X,
      HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{max u w} := by
  intro U
  exact (addCommGrpHasSheafifyOver X U).isRightAdjoint

/-- Local bijectivity for abelian-group-valued presheaves is detected on every slice of an
opens site in a coefficient universe containing the space. -/
instance addCommGrpWEqualsLocallyBijectiveOver (X : TopCat.{u}) :
    ∀ U : Opens X,
      ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{max u w} := by
  intro U
  -- Mathlib's concrete-site criterion uses the coefficient universe for the site.
  -- Transport to its standard small model to apply that criterion at `max u w`.
  let J := (Opens.grothendieckTopology X).over U
  let K := (equivSmallModel.{max u w} (Over U)).inverse.inducedTopology J
  letI : ∀ V : SmallModel.{max u w} (Over U), CategoryTheory.Limits.PreservesColimitsOfShape
      (K.Cover V)ᵒᵖ (forget AddCommGrpCat.{max u w}) := fun V => by
    letI : FinallySmall.{max u w} (K.Cover V)ᵒᵖ :=
      finallySmall_of_essentiallySmall _
    exact FinallySmall.preservesColimitsOfShape_of_isFiltered
      (K.Cover V)ᵒᵖ (forget AddCommGrpCat.{max u w})
  letI : K.WEqualsLocallyBijective AddCommGrpCat.{max u w} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

/-- Abelian-group-valued weak sheafification is available on every twice-sliced opens site,
with coefficients in a universe containing the space. -/
instance addCommGrpHasWeakSheafifyOverOver (X : TopCat.{u}) :
    ∀ (U : Opens X) (V : Over U),
      HasWeakSheafify (((Opens.grothendieckTopology X).over U).over V)
        AddCommGrpCat.{max u w} := by
  intro U V
  letI := addCommGrpHasSheafifyOver X V.left
  exact (Equivalence.hasSheafify (((Opens.grothendieckTopology X).over U).over V)
    ((Opens.grothendieckTopology X).over V.left) V.iteratedSliceEquiv
    AddCommGrpCat.{max u w}).isRightAdjoint

/-- Local bijectivity for abelian-group-valued presheaves is detected on every twice-sliced
opens site in a coefficient universe containing the space. -/
instance addCommGrpWEqualsLocallyBijectiveOverOver (X : TopCat.{u}) :
    ∀ (U : Opens X) (V : Over U),
      (((Opens.grothendieckTopology X).over U).over V).WEqualsLocallyBijective
        AddCommGrpCat.{max u w} := by
  intro U V
  letI := (V.iteratedSliceEquiv.sheafCongr
    (((Opens.grothendieckTopology X).over U).over V)
    ((Opens.grothendieckTopology X).over V.left)
    AddCommGrpCat.{max u w}).isEquivalence_functor
  exact GrothendieckTopology.WEqualsLocallyBijective.transport
    (((Opens.grothendieckTopology X).over U).over V)
    ((Opens.grothendieckTopology X).over V.left) V.iteratedSliceEquiv.inverse
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

end TopCat

