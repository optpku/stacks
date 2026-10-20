/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.Representable
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open CategoryTheory.GrothendieckTopology

universe u v

/- Lemma 35.39.1: for a covering family in a chosen big standard site, explicit
representable gluing is an equivalence from slice-object descent data to sheaves whose products
with all covering representables are representable. -/
@[stacks 02W5] #check
  (AlgebraicGeometry.ChosenBigSite.RepresentableDescent.glueIsEquivalence :
    ∀ (τ : StandardTopology) (𝒮 : ChosenBigSite.{u, v} τ.precoverage)
      {S : 𝒮.carrier} {I : Type (max u v)} {Sᵢ : I → 𝒮.carrier}
      (p : ∀ i, Sᵢ i ⟶ S)
      (hcover : Sieve.ofArrows Sᵢ p ∈ 𝒮.toGrothendieck S),
      -- Local instance justification (defeq pin): expose the chosen site's stored pullbacks in this complete type.
      letI : HasPullbacks 𝒮.carrier := 𝒮.hasPullbacks
      -- Local instance justification (defeq pin): expose named standard-site subcanonicity in this complete type.
      letI : 𝒮.toGrothendieck.Subcanonical :=
        AlgebraicGeometry.ChosenBigSite.standardSubcanonical τ 𝒮
      Functor.IsEquivalence
        (CategoryTheory.GrothendieckTopology.RepresentableDescent.glue
          𝒮.toGrothendieck p hcover))

/- The representing object for each local product is the corresponding local slice object. -/
#check
  (AlgebraicGeometry.ChosenBigSite.RepresentableDescent.productIso :
    ∀ (τ : StandardTopology) (𝒮 : ChosenBigSite.{u, v} τ.precoverage)
      {S : 𝒮.carrier} {I : Type (max u v)} {Sᵢ : I → 𝒮.carrier}
      (p : ∀ i, Sᵢ i ⟶ S)
      (hcover : Sieve.ofArrows Sᵢ p ∈ 𝒮.toGrothendieck S),
      -- Local instance justification (defeq pin): expose the chosen site's stored pullbacks in this complete type.
      letI : HasPullbacks 𝒮.carrier := 𝒮.hasPullbacks
      -- Local instance justification (defeq pin): expose named standard-site subcanonicity in this complete type.
      letI : 𝒮.toGrothendieck.Subcanonical :=
        AlgebraicGeometry.ChosenBigSite.standardSubcanonical τ 𝒮
      ∀ (D : Over.pseudofunctor.DescentData p) (i : I),
        Limits.prod
            ((𝒮.toGrothendieck.over S).uliftYoneda.{max u v}.obj (Over.mk (p i)))
            ((CategoryTheory.GrothendieckTopology.RepresentableDescent.glue
              𝒮.toGrothendieck p hcover).obj D).obj ≅
          (𝒮.toGrothendieck.over S).uliftYoneda.{max u v}.obj
            (CategoryTheory.GrothendieckTopology.RepresentableDescent.localObject p D i))

/- The glued sheaf is representable exactly when its slice descent datum is effective. -/
#check
  (AlgebraicGeometry.ChosenBigSite.RepresentableDescent.representable_iff_effective :
    ∀ (τ : StandardTopology) (𝒮 : ChosenBigSite.{u, v} τ.precoverage)
      {S : 𝒮.carrier} {I : Type (max u v)} {Sᵢ : I → 𝒮.carrier}
      (p : ∀ i, Sᵢ i ⟶ S)
      (hcover : Sieve.ofArrows Sᵢ p ∈ 𝒮.toGrothendieck S),
      -- Local instance justification (defeq pin): expose the chosen site's stored pullbacks in this complete type.
      letI : HasPullbacks 𝒮.carrier := 𝒮.hasPullbacks
      -- Local instance justification (defeq pin): expose named standard-site subcanonicity in this complete type.
      letI : 𝒮.toGrothendieck.Subcanonical :=
        AlgebraicGeometry.ChosenBigSite.standardSubcanonical τ 𝒮
      ∀ D : Over.pseudofunctor.DescentData p,
        ((𝒮.toGrothendieck.over S).uliftYoneda.{max u v}).essImage
            ((CategoryTheory.GrothendieckTopology.RepresentableDescent.glue
              𝒮.toGrothendieck p hcover).obj D).obj ↔
          Over.DescentData.IsEffective D)
