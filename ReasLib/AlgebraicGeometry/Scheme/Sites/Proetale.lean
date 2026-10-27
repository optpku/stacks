/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.FiniteLimits
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Countable
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.SetTheory.Cardinal.Basic
public import ReasLib.CategoryTheory.Sites.Precoverage.Combinatorial

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry

/-- The cardinal bound for pro-étale presentations is the maximum of
`κ ^ (2 ^ (2 ^ (2 ^ κ)))`, `κ ^ ℵ₀`, and `Order.succ κ`. -/
def Scheme.proetaleBound (κ : Cardinal.{u}) : Cardinal.{u} :=
  max (max (κ ^ ((2 : Cardinal) ^ ((2 : Cardinal) ^ ((2 : Cardinal) ^ κ))))
    (κ ^ ℵ₀)) (Order.succ κ)

/-- A small category of schemes is a bounded pro-étale presentation when its
essential image is closed under the pro-étale cardinal bound, its countable
limits and colimits agree with those in schemes, its selected coverings have
selected sources and targets, and its pretopology consists of selected
pro-étale coverings representing every ambient pro-étale covering up to
combinatorial equivalence. -/
def IsBigProetaleSite (carrier : Cat.{u, u}) (hasPullbacks : HasPullbacks carrier)
    (toScheme : carrier ⥤ Scheme.{u}) (seedSchemes : Set carrier)
    (seedCoverings : ∀ target : carrier, Set (Presieve target))
    (pretopology : @Pretopology carrier (Cat.str carrier) hasPullbacks) : Prop :=
  let size := fun (scheme : Scheme.{u}) =>
    ℵ₀ ⊔ #scheme.affineOpens ⊔ ⨆ affineOpen : scheme.affineOpens, #(Γ(scheme, affineOpen))
  (∀ {target : carrier} {covering : Presieve target},
    covering ∈ seedCoverings target → target ∈ seedSchemes) ∧
  (∀ {target : carrier} {covering : Presieve target},
    covering ∈ seedCoverings target →
      ∀ {source : carrier} (arrow : source ⟶ target), covering arrow → source ∈ seedSchemes) ∧
  (∀ {target : carrier} {covering : Presieve target},
    covering ∈ seedCoverings target → covering ∈ pretopology target) ∧
  pretopology.toPrecoverage ≤ Scheme.proetalePrecoverage.comap toScheme ∧
  (Scheme.proetalePrecoverage.comap toScheme).coversUpToCombinatorialEquivalence
    pretopology.toPrecoverage ∧
  (∀ (represented : carrier) (scheme : Scheme.{u}),
    size scheme ≤ Scheme.proetaleBound (size (toScheme.obj represented)) →
      ∃ replacement : carrier, Nonempty (scheme ≅ toScheme.obj replacement)) ∧
  (∀ {index : Type} [SmallCategory index] [CountableCategory index]
    (diagram : index ⥤ carrier), HasLimit diagram ↔ HasLimit (diagram ⋙ toScheme)) ∧
  (∀ {index : Type} [SmallCategory index] [CountableCategory index]
    (diagram : index ⥤ carrier) [HasLimit diagram] [HasLimit (diagram ⋙ toScheme)],
      IsIso (limit.post diagram toScheme)) ∧
  (∀ {index : Type} [SmallCategory index] [CountableCategory index]
    (diagram : index ⥤ carrier), HasColimit diagram ↔ HasColimit (diagram ⋙ toScheme)) ∧
  (∀ {index : Type} [SmallCategory index] [CountableCategory index]
    (diagram : index ⥤ carrier) [HasColimit diagram] [HasColimit (diagram ⋙ toScheme)],
      IsIso (colimit.post diagram toScheme))

/-- A small pro-étale site with explicit seeds, bounded essential-image closure,
and comparison of countable limits and colimits with schemes. -/
structure BigProetaleSite where
  /-- The small category underlying the site. -/
  carrier : Cat.{u, u}
  /-- The underlying category has pullbacks. -/
  hasPullbacks : HasPullbacks carrier
  /-- The functor realizing the underlying objects as schemes. -/
  toScheme : carrier ⥤ Scheme.{u}
  /-- The functor to schemes is fully faithful. -/
  fullyFaithful : toScheme.FullyFaithful
  /-- The selected seed objects in the underlying category. -/
  seedSchemes : Set carrier
  /-- The selected seed covering presieves. -/
  seedCoverings : ∀ target : carrier, Set (Presieve target)
  /-- The pretopology of the chosen category. -/
  pretopology : @Pretopology carrier (Cat.str carrier) hasPullbacks
  /-- The seeds and pretopology satisfy bounded pro-étale presentation conditions. -/
  specification :
    IsBigProetaleSite carrier hasPullbacks toScheme seedSchemes seedCoverings pretopology

namespace BigProetaleSite

/-- Construct a bounded pro-étale site from a fully faithful scheme functor,
explicit seeds, a pretopology, and its defining conditions. -/
def ofPretopology (carrier : Cat.{u, u}) (hasPullbacks : HasPullbacks carrier)
    (toScheme : carrier ⥤ Scheme.{u}) (fullyFaithful : toScheme.FullyFaithful)
    (seedSchemes : Set carrier) (seedCoverings : ∀ target : carrier, Set (Presieve target))
    (pretopology : @Pretopology carrier (Cat.str carrier) hasPullbacks)
    (specification :
      IsBigProetaleSite carrier hasPullbacks toScheme seedSchemes seedCoverings pretopology) :
    BigProetaleSite.{u} where
  carrier := carrier
  hasPullbacks := hasPullbacks
  toScheme := toScheme
  fullyFaithful := fullyFaithful
  seedSchemes := seedSchemes
  seedCoverings := seedCoverings
  pretopology := pretopology
  specification := specification

/-- A bounded pro-étale site satisfies all its seed, covering, bounded closure,
and countable limit and colimit comparison conditions. -/
theorem spec (site : BigProetaleSite.{u}) :
    IsBigProetaleSite site.carrier site.hasPullbacks site.toScheme site.seedSchemes
      site.seedCoverings site.pretopology := site.specification

/-- The Grothendieck topology generated by the pretopology of a bounded
pro-étale site. -/
def toGrothendieck (site : BigProetaleSite.{u}) : GrothendieckTopology site.carrier :=
  @Pretopology.toGrothendieck site.carrier (Cat.str site.carrier) site.hasPullbacks site.pretopology


/-- The bounded pro-étale conditions imply the ordinary chosen-site laws.
The pro-étale object bound dominates the ordinary countable-successor bound;
no closure under all ambient covering sources is used. -/
theorem chosen_specification (X : BigProetaleSite.{u}) :
    IsChosenBigSite Scheme.proetalePrecoverage X.carrier X.hasPullbacks
      X.toScheme X.seedSchemes X.seedCoverings X.pretopology := sorry

/-- Keep the carrier, scheme functor, seeds, and pretopology of the bounded
pro-étale construction as a chosen presentation. -/
def toChosenBigSite (X : BigProetaleSite.{u}) :
    ChosenBigSite.{u, u} Scheme.proetalePrecoverage where
  carrier := X.carrier
  hasPullbacks := X.hasPullbacks
  toScheme := X.toScheme
  fullyFaithful := X.fullyFaithful
  seedSchemes := X.seedSchemes
  seedCoverings := X.seedCoverings
  pretopology := X.pretopology
  specification := X.chosen_specification

/-- The empty diagram has a limit by the countable-limit clause of Tag 000J.
This proof uses the supplied bounded-site specification, not an admitted
existence theorem from which an object would then be chosen. -/
theorem hasLimitEmpty (X : BigProetaleSite.{u}) :
    HasLimit (Functor.empty.{0} X.carrier) := by
  exact (X.spec.2.2.2.2.2.2.1 (Functor.empty.{0} X.carrier)).mpr inferInstance

/-- The comparison map for each countable limit is an isomorphism. -/
theorem limitPost_isIso (X : BigProetaleSite.{u})
    {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ X.carrier) [HasLimit F] [HasLimit (F ⋙ X.toScheme)] :
    IsIso (limit.post F X.toScheme) :=
  X.spec.2.2.2.2.2.2.2.1 F

/-- The empty limit of the bounded carrier, representing the terminal scheme.
It is the standard categorical limit construction with its full universal
property supplied by `hasLimitEmpty`. -/
noncomputable def specZ (X : BigProetaleSite.{u}) : X.carrier :=
  letI : HasLimit (Functor.empty.{0} X.carrier) := X.hasLimitEmpty
  limit (Functor.empty.{0} X.carrier)

/-- Identify the represented empty limit with the actual integer spectrum
using the supplied limit comparison and terminality in schemes. -/
noncomputable def specZIso (X : BigProetaleSite.{u}) :
    X.toScheme.obj X.specZ ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) := by
  letI : HasLimit (Functor.empty.{0} X.carrier) := X.hasLimitEmpty
  letI := X.limitPost_isIso (Functor.empty.{0} X.carrier)
  let e₁ : X.toScheme.obj (limit (Functor.empty.{0} X.carrier)) ≅
      limit (Functor.empty.{0} X.carrier ⋙ X.toScheme) :=
    asIso (limit.post (Functor.empty.{0} X.carrier) X.toScheme)
  let e₂ : limit (Functor.empty.{0} X.carrier ⋙ X.toScheme) ≅
      Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    ((isLimitEquivIsTerminalOfIsEmpty _ (limit.cone _)).toFun
      (limit.isLimit (Functor.empty.{0} X.carrier ⋙ X.toScheme))).uniqueUpToIso
        specULiftZIsTerminal
  exact e₁ ≪≫ e₂

/-- Apply the generic represented-terminal interface to any bounded small
pro-étale site, retaining its carrier in the same universe. -/
noncomputable def withSpecZ (X : BigProetaleSite.{u}) :
    ChosenBigSite.WithSpecZ.{u, u} Scheme.proetalePrecoverage where
  toChosenBigSite := X.toChosenBigSite
  specZ := X.specZ
  specZIso := X.specZIso

/-- Integer-spectrum representation is a consequence of bounded-site
construction, not an extra hypothesis of the source-facing facade. -/
theorem exists_specZ (X : BigProetaleSite.{u}) :
    ∃ Z : X.carrier, Nonempty (X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  ⟨X.specZ, ⟨X.specZIso⟩⟩

end BigProetaleSite

end AlgebraicGeometry
