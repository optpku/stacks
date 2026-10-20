/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}}

/-- Composition with an étale morphism `j : U ⟶ X` sends the small étale site of
`U` to the small étale site of `X`. -/
abbrev etaleRestriction (j : U ⟶ X) [Etale j] : U.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map (P := @Etale) (Q := (⊤ : MorphismProperty Scheme))
    (f := j) (inferInstance : Etale j)

/-- The étale site restriction functor is induced by composition with the
étale morphism. -/
theorem etaleRestriction_def (j : U ⟶ X) [Etale j] :
    etaleRestriction j =
      MorphismProperty.Over.map (P := @Etale) (Q := (⊤ : MorphismProperty Scheme))
        (f := j) (inferInstance : Etale j) := sorry

/-- Composition with an étale morphism is continuous for the small étale
topologies. -/
instance etaleRestriction_isContinuous (j : U ⟶ X) [Etale j] :
    Functor.IsContinuous (etaleRestriction j) U.smallEtaleTopology X.smallEtaleTopology := sorry

end AlgebraicGeometry.Scheme
