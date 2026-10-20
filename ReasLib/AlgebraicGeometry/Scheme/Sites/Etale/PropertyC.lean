/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.OpenImmersion
public import ReasLib.CategoryTheory.Sites.DenseSubsite.Reflection
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

/-- Property (C) for a scheme morphism: every small étale object over the
source is covered by the pullback of a small étale object over the target. -/
def hasPropertyC {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (U : X.Etale),
    ∃ (V : Y.Etale) (h : pullback f V.hom ⟶ U.left),
      Surjective h ∧ h ≫ U.hom = pullback.fst f V.hom

/-- Property (C) is equivalent to its explicit étale-object presentation. -/
theorem hasPropertyC_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    hasPropertyC f ↔
      ∀ (U : X.Etale),
        ∃ (V : Y.Etale) (h : pullback f V.hom ⟶ U.left),
          Surjective h ∧ h ≫ U.hom = pullback.fst f V.hom := sorry

/-- Property (C) makes small étale pullback cover-dense. -/
theorem smallEtalePullback_isCoverDense_of_hasPropertyC
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hC : hasPropertyC f) :
    (Scheme.smallEtalePullback f).IsCoverDense X.smallEtaleTopology := sorry

/-- Every open immersion of schemes satisfies the quantified form of
Property (C). -/
theorem openImmersion_hasPropertyC
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    ∀ (U : X.Etale),
      ∃ (V : Y.Etale) (h : pullback f V.hom ⟶ U.left),
        Surjective h ∧ h ≫ U.hom = pullback.fst f V.hom := sorry

/-- An integral morphism whose underlying map is a closed embedding satisfies
Property (C). -/
theorem hasPropertyC_of_isIntegralHom_isClosedEmbedding
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    (hf : Topology.IsClosedEmbedding f.base) : hasPropertyC f := sorry

end AlgebraicGeometry.Scheme.Etale.SmallToBig
