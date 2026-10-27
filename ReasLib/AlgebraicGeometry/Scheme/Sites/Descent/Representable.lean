/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard
public import ReasLib.CategoryTheory.Sites.Descent.Representable

/-!
# Representable descent on chosen big standard sites

This module specializes representable descent to chosen presentations of the big sites for the
standard scheme topologies.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

universe u v

namespace AlgebraicGeometry.ChosenBigSite

/-- The Grothendieck topology of a chosen big standard site is subcanonical. -/
theorem standardSubcanonical (τ : StandardTopology)
    (𝒮 : ChosenBigSite.{u, v} τ.precoverage) : 𝒮.toGrothendieck.Subcanonical := sorry

namespace RepresentableDescent

variable (τ : StandardTopology) (𝒮 : ChosenBigSite.{u, v} τ.precoverage)

-- Local instance justification (defeq pin): use the stored pullbacks while specializing the generic representable-descent construction.
local instance : HasPullbacks 𝒮.carrier := 𝒮.hasPullbacks

-- Local instance justification (defeq pin): use named standard-site subcanonicity only within this representable-descent specialization.
local instance : 𝒮.toGrothendieck.Subcanonical := standardSubcanonical τ 𝒮

/-- Representable gluing along a covering family in a chosen big standard site is an
equivalence from slice descent data to locally representable sheaves. -/
theorem glueIsEquivalence {S : 𝒮.carrier} {I : Type (max u v)}
    {Sᵢ : I → 𝒮.carrier} (p : ∀ i, Sᵢ i ⟶ S)
    (hcover : Sieve.ofArrows Sᵢ p ∈ 𝒮.toGrothendieck S) :
    Functor.IsEquivalence
      (CategoryTheory.GrothendieckTopology.RepresentableDescent.glue
        𝒮.toGrothendieck p hcover) := sorry

/-- The product of a covering representable with a glued sheaf is represented by the
corresponding local slice object of the descent datum. -/
noncomputable def productIso {S : 𝒮.carrier} {I : Type (max u v)}
    {Sᵢ : I → 𝒮.carrier} (p : ∀ i, Sᵢ i ⟶ S)
    (hcover : Sieve.ofArrows Sᵢ p ∈ 𝒮.toGrothendieck S)
    (D : Over.pseudofunctor.DescentData p) (i : I) :
    Limits.prod
        ((𝒮.toGrothendieck.over S).uliftYoneda.{max u v}.obj (Over.mk (p i)))
        ((CategoryTheory.GrothendieckTopology.RepresentableDescent.glue
          𝒮.toGrothendieck p hcover).obj D).obj ≅
      (𝒮.toGrothendieck.over S).uliftYoneda.{max u v}.obj
        (CategoryTheory.GrothendieckTopology.RepresentableDescent.localObject p D i) :=
  CategoryTheory.GrothendieckTopology.RepresentableDescent.productIso
    𝒮.toGrothendieck p hcover D i

/-- The forward map of the local product isomorphism is the explicit descent comparison. -/
theorem productIso_hom {S : 𝒮.carrier} {I : Type (max u v)}
    {Sᵢ : I → 𝒮.carrier} (p : ∀ i, Sᵢ i ⟶ S)
    (hcover : Sieve.ofArrows Sᵢ p ∈ 𝒮.toGrothendieck S)
    (D : Over.pseudofunctor.DescentData p) (i : I) :
    (productIso τ 𝒮 p hcover D i).hom =
      CategoryTheory.GrothendieckTopology.RepresentableDescent.productComparisonHom
        𝒮.toGrothendieck p hcover D i := sorry

/-- A sheaf glued from slice descent data is representable exactly when the datum is
effective. -/
theorem representable_iff_effective {S : 𝒮.carrier} {I : Type (max u v)}
    {Sᵢ : I → 𝒮.carrier} (p : ∀ i, Sᵢ i ⟶ S)
    (hcover : Sieve.ofArrows Sᵢ p ∈ 𝒮.toGrothendieck S)
    (D : Over.pseudofunctor.DescentData p) :
    ((𝒮.toGrothendieck.over S).uliftYoneda.{max u v}).essImage
        ((CategoryTheory.GrothendieckTopology.RepresentableDescent.glue
          𝒮.toGrothendieck p hcover).obj D).obj ↔
      Over.DescentData.IsEffective Sᵢ p D := sorry

end RepresentableDescent

end AlgebraicGeometry.ChosenBigSite
