/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic

/-!
# Canonical small scheme sites

This module packages the canonical small Zariski and étale sites and the small
presentations of all five standard sites, together with their topologies and
forgetful functors.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The two standard topologies admitting a canonical small scheme site. -/
inductive SmallStandardTopology where
  /-- The small Zariski topology. -/
  | zariski
  /-- The small étale topology. -/
  | etale

namespace SmallStandardTopology

/-- The standard big topology corresponding to a standard small topology. -/
def toStandard : SmallStandardTopology → StandardTopology
  | .zariski => .zariski
  | .etale => .etale

/-- The two small choices correspond respectively to the Zariski and étale standard
topologies. -/
theorem toStandard_spec :
    toStandard .zariski = .zariski ∧ toStandard .etale = .etale := ⟨rfl, rfl⟩

/-- The category underlying the selected small site of `S`. -/
def site (σ : SmallStandardTopology) (S : Scheme.{u}) : Cat.{u, u + 1} :=
  match σ with
  | .zariski => Cat.of S.smallZariskiSite
  | .etale => Cat.of S.Etale

/-- The selected small-site category is the canonical Zariski or étale site. -/
theorem site_spec (σ : SmallStandardTopology) (S : Scheme.{u}) :
    site σ S = match σ with
      | .zariski => Cat.of S.smallZariskiSite
      | .etale => Cat.of S.Etale := by
  cases σ <;> rfl

/-- The Grothendieck topology on the selected small site of `S`. -/
def topology (σ : SmallStandardTopology) (S : Scheme.{u}) :
    GrothendieckTopology (site σ S) :=
  match σ with
  | .zariski => S.smallZariskiTopology
  | .etale => S.smallEtaleTopology

/-- The selected topology is the canonical small Zariski or small étale topology. -/
theorem topology_spec (σ : SmallStandardTopology) (S : Scheme.{u}) :
    topology σ S = match σ with
      | .zariski => S.smallZariskiTopology
      | .etale => S.smallEtaleTopology := by
  cases σ <;> rfl

/-- The canonical functor from the selected small site to schemes over `S`. -/
def toOver (σ : SmallStandardTopology) (S : Scheme.{u}) : site σ S ⥤ Over S :=
  match σ with
  | .zariski => S.smallZariskiForget
  | .etale => MorphismProperty.Over.forget @Etale ⊤ S

/-- The selected functor to `Over S` is the canonical Zariski or étale forgetful functor. -/
theorem toOver_spec (σ : SmallStandardTopology) (S : Scheme.{u}) :
    toOver σ S = match σ with
      | .zariski => S.smallZariskiForget
      | .etale => MorphismProperty.Over.forget @Etale ⊤ S := by
  cases σ <;> rfl

/-- The source-scheme functor on the selected small site. -/
abbrev toScheme (σ : SmallStandardTopology) (S : Scheme.{u}) : site σ S ⥤ Scheme.{u} :=
  toOver σ S ⋙ Over.forget S

/-- The selected source-scheme functor forgets the morphism to `S`. -/
theorem toScheme_spec (σ : SmallStandardTopology) (S : Scheme.{u}) :
    toScheme σ S = toOver σ S ⋙ Over.forget S := rfl

end SmallStandardTopology

namespace StandardTopology.Small

/-- The morphism property defining the small site for a standard topology. -/
def morphismProperty (τ : StandardTopology) : MorphismProperty Scheme :=
  match τ with
  | .zariski => @IsOpenImmersion
  | .etale => @Etale
  | .smooth => @Smooth
  | .syntomic => @Syntomic
  | .fppf => @Flat ⊓ @LocallyOfFinitePresentation

/-- The small-site morphism property is the expected one for each standard
topology. -/
theorem morphismProperty_def (τ : StandardTopology) :
    morphismProperty τ = match τ with
      | .zariski => @IsOpenImmersion
      | .etale => @Etale
      | .smooth => @Smooth
      | .syntomic => @Syntomic
      | .fppf => @Flat ⊓ @LocallyOfFinitePresentation := sorry

/-- The morphism property defining a small standard site is stable under base
change. -/
instance morphismPropertyIsStableUnderBaseChange (τ : StandardTopology) :
    (morphismProperty τ).IsStableUnderBaseChange := sorry

/-- The morphism property defining a small standard site is multiplicative. -/
instance morphismPropertyIsMultiplicative (τ : StandardTopology) :
    (morphismProperty τ).IsMultiplicative := sorry

/-- The morphism property defining a small standard site respects
isomorphisms. -/
instance morphismPropertyRespectsIso (τ : StandardTopology) :
    (morphismProperty τ).RespectsIso := sorry

/-- The category underlying the small site for `τ` over `S`. -/
abbrev site (τ : StandardTopology) (S : Scheme.{u}) : Cat.{u, u + 1} :=
  Cat.of ((morphismProperty τ).Over ⊤ S)

/-- The small standard site is the category of morphisms to `S` satisfying
`morphismProperty τ`. -/
theorem site_def (τ : StandardTopology) (S : Scheme.{u}) :
    site τ S = Cat.of ((morphismProperty τ).Over ⊤ S) := sorry

/-- The Grothendieck topology on the small standard `τ`-site of `S`. -/
abbrev topology (τ : StandardTopology) (S : Scheme.{u}) :
    GrothendieckTopology (site τ S) :=
  S.smallGrothendieckTopology (morphismProperty τ)

/-- The small standard topology is induced from the corresponding topology on
schemes. -/
theorem topology_def (τ : StandardTopology) (S : Scheme.{u}) :
    topology τ S = S.smallGrothendieckTopology (morphismProperty τ) := sorry

/-- The canonical functor from the small standard `τ`-site to schemes over
`S`. -/
abbrev toOver (τ : StandardTopology) (S : Scheme.{u}) : site τ S ⥤ Over S :=
  MorphismProperty.Over.forget (morphismProperty τ) ⊤ S

/-- The small-site functor remembers the underlying scheme over `S`. -/
theorem toOver_def (τ : StandardTopology) (S : Scheme.{u}) :
    toOver τ S = MorphismProperty.Over.forget (morphismProperty τ) ⊤ S := sorry

end StandardTopology.Small

end AlgebraicGeometry
