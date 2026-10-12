/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Postcomposition étaleness on small étale sites

The site functor `j : X_étale ⥤ Y_étale` of an étale morphism of algebraic spaces is
`etaleRestriction`. This sibling records only that postcomposition of structure morphisms
remains étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Postcomposition of an étale morphism from a scheme with an étale morphism of algebraic spaces
remains étale. -/
instance etale_hom_comp (f : X ⟶ Y) [Etale f] (U : smallEtaleSite X) :
    Etale (U.hom ≫ f) :=
  @Etale.etale_comp S _ X U.hom Y f U.prop ‹_›

end AlgebraicGeometry.AlgebraicSpace
