/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.AdjoinVariable.Family
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Family
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-!
# Indexed exterior or divided-power generators

The reusable graded owner is a relative family extension in one fixed degree. It keeps the base
inclusion, all homogeneous generators, the divided-power relative mapping property, and
finite-subset descent in one object. The chain-DGA companion adds the attaching differentials and
forgets to this graded presentation. Thus odd exterior behavior and even divided-power behavior are
consequences of the parity of the common degree, rather than two unrelated ungraded models.
-/

universe u v w

namespace DividedPowerGradedAlgebra.Adjoin

variable {R : Type u} [CommRing R]
variable (A : DividedPowerGradedAlgebra.{u, v} R) (d : ℕ+) (J : Type w) [Small.{v} J]

/- Remark 23.6.4 (0F4I): a possibly infinite family of homogeneous generators in one fixed
positive degree has a graded divided-power extension with the relative mapping property. -/
@[stacks 0F4I "indexed exterior or divided-power generators"]
#check (Family.nonempty A (d : ℕ) J :
  Nonempty (Family A (d : ℕ) J))

/- Remark 23.6.4 (0F4I), directed-colimit clause: the full indexed graded extension has the
universal property of the compatible system of its finite-subset extensions. -/
@[stacks 0F4I "indexed extension as the finite-subset colimit"]
#check (Family.FiniteSubset.isColimit (A := A) (d := (d : ℕ)) :
  ∀ (Y : Family A (d : ℕ) J)
    (X : ∀ E : Finset J, Family A (d : ℕ) E),
    IsColimit (Family.FiniteSubset.cocone Y X))

#check @Family.FiniteSubset.existsUnique_desc (A := A) (d := (d : ℕ))

/- The graded owner exposes the reusable presentation and finite-subset descent data. -/
#check @Family
#check @Presentation
#check @Presentation.ofIso
#check @Family.lift
#check @Family.existsUnique_lift
#check @Family.reindex
#check @Family.reindex_id
#check @Family.reindex_comp
#check @Family.IsComparison
#check @Family.comparison_isComparison
#check @Family.IsComparison.eq
#check @Family.existsUnique_comparison
#check @Family.comparisonIso
#check @Family.comparisonIso_hom
#check @Family.comparisonIso_inv
#check @Family.comparisonIso_self
#check @Family.comparisonIso_symm
#check @Family.comparisonIso_trans
#check @Family.FiniteSubset.comparisonNatIso
#check @Family.FiniteSubset.comparisonNatIso_hom_app
#check @Family.FiniteSubset.comparisonNatIso_inv_app
#check @Family.FiniteSubset.map
#check @Family.FiniteSubset.comparison_naturality
#check @Family.FiniteSubset.map_refl
#check @Family.FiniteSubset.toIndexed
#check @Family.FiniteSubset.toIndexed_comp_map
#check @Family.FiniteSubset.toIndexed_comp_comparison
#check @Family.FiniteSubset.inclusion_comp_toIndexed
#check @Family.FiniteSubset.toIndexed_generator
#check @Family.FiniteSubset.IsCompatible
#check @Family.FiniteSubset.isCompatible_iff
#check @Family.FiniteSubset.descBase
#check @Family.FiniteSubset.descGenerator
#check @Family.FiniteSubset.desc
#check @Family.FiniteSubset.IsDesc
#check @Family.FiniteSubset.isDesc_iff
#check @Family.FiniteSubset.desc_isDesc
#check @Family.FiniteSubset.desc_comp_toIndexed
#check @Family.FiniteSubset.desc_unique
#check @Family.FiniteSubset.diagram
#check @Family.FiniteSubset.cocone
#check @Family.FiniteSubset.coconeMap
#check @Family.FiniteSubset.colimitDesc
#check @Family.FiniteSubset.isColimit

end DividedPowerGradedAlgebra.Adjoin

namespace DividedPowerChainAlgebra.Adjoin

variable {R : Type u} [CommRing R]
variable (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (J : Type w) [Small.{v} J]
variable (f : J → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1))
variable (hf : ∀ j : J, IsCycle A d (f j))

/- Chain-DGA companion: the same family owner retains the prescribed attaching differentials, while
the graded facade above is the source-level reusable colimit API. -/
#check Family.nonempty A d f hf

/- The chain-DGA finite-subset colimit is retained as a differential companion. -/
#check @Family.FiniteSubset.existsUnique_desc

/- Forgetting the differential exposes the source-level graded adjoining-family object. -/
#check @Family.toGradedFamily
#check @Family.toCell
#check @Cell.GradedPresentation
#check @Cell.toFamily
#check @Cell.toFamily_toCell
#check @Family.toCell_toFamily
#check @DividedPowerGradedAlgebra.Adjoin.Family
#check @DividedPowerGradedAlgebra.Adjoin.Presentation

/- The family owner exposes the differential equation and the complete relative mapping property. -/
#check @Family.attaching_isCycle
#check @Family.differential_generator
#check @Family.existsUnique_lift
#check @Family.reindex
#check @Family.reindex_toGradedHom
#check @Family.reindex_id
#check @Family.reindex_comp
#check @Family.IsComparison
#check @Family.comparison_isComparison
#check @Family.IsComparison.eq
#check @Family.existsUnique_comparison
#check @Family.comparisonIso
#check @Family.comparisonIso_hom
#check @Family.comparisonIso_inv
#check @Family.comparisonIso_self
#check @Family.comparisonIso_symm
#check @Family.comparisonIso_trans
#check @Family.comparison_toGradedHom
#check @Family.comparisonIso_toGradedIso

/- Finite-subset transition maps and the descended morphism are explicit reusable data. -/
#check @Family.FiniteSubset.map
#check @Family.FiniteSubset.map_toGradedHom
#check @Family.FiniteSubset.map_refl
#check @Family.FiniteSubset.comparison_naturality
#check @Family.FiniteSubset.toIndexed_comp_map
#check @Family.FiniteSubset.comparisonNatIso
#check @Family.FiniteSubset.comparisonNatIso_hom_app
#check @Family.FiniteSubset.comparisonNatIso_inv_app
#check @Family.FiniteSubset.toIndexed
#check @Family.FiniteSubset.toIndexed_toGradedHom
#check @Family.FiniteSubset.toIndexed_comp_comparison
#check @Family.FiniteSubset.inclusion_comp_toIndexed
#check @Family.FiniteSubset.toIndexed_generator
#check @Family.FiniteSubset.IsCompatible
#check @Family.FiniteSubset.isCompatible_iff
#check @Family.FiniteSubset.desc
#check @Family.FiniteSubset.desc_comp_toIndexed
#check @Family.FiniteSubset.desc_toGradedHom
#check @Family.FiniteSubset.IsDesc
#check @Family.FiniteSubset.isDesc_iff
#check @Family.FiniteSubset.diagram
#check @Family.FiniteSubset.cocone
#check @Family.FiniteSubset.coconeMap
#check @Family.FiniteSubset.colimitDesc
#check @Family.FiniteSubset.isColimit

/- In odd degree, strict graded commutativity makes every indexed generator exterior. -/
#check @Family.generator_sq_eq_zero
#check @DividedPowerGradedAlgebra.Adjoin.Family.generator_sq_eq_zero

end DividedPowerChainAlgebra.Adjoin
