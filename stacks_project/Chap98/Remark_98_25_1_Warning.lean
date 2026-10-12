/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import stacks_project.Chap98.Lemma_98_25_2_Noetherian

/-!
# The Noetherian site does not have fibre products

The site `(Noetherian/S)_τ` does not have fibre products, so the continuous
inclusion into `(Sch/S)_τ` does not define a morphism of sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.StandardTopology

universe u

namespace AlgebraicGeometry

/-- Remark 98.25.1 (Warning) (1): the site `(Noetherian/S)_τ` does not have
fibre products. -/
@[stacks 0GE2]
theorem not_hasPullbacks_locallyNoetherian
    (S : Scheme.{u}) [IsLocallyNoetherian S] [Nonempty S] :
    ¬ HasPullbacks (locallyNoetherian S).FullSubcategory := sorry

/-- Remark 98.25.1 (Warning) (2): the continuous inclusion
`(Noetherian/S)_τ ⥤ (Sch/S)_τ` does not define a morphism of sites.
Examples, Section 110.60 treats the case `τ = fppf`. -/
@[stacks 0GE2]
theorem not_isMorphismOfSites_locallyNoetherianInclusion
    (S : Scheme.{u}) [IsLocallyNoetherian S] [Nonempty S]
    (τ : StandardTopology) :
    ¬ IsMorphismOfSites (locallyNoetherianTopology τ S) (τ.overTopology S)
        (locallyNoetherian S).ι := sorry

end AlgebraicGeometry
