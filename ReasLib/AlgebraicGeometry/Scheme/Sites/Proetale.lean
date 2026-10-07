module

public import Mathlib.AlgebraicGeometry.AffineScheme
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
      site.seedCoverings site.pretopology := sorry

/-- The Grothendieck topology generated by the pretopology of a bounded
pro-étale site. -/
def toGrothendieck (site : BigProetaleSite.{u}) : GrothendieckTopology site.carrier :=
  @Pretopology.toGrothendieck site.carrier (Cat.str site.carrier) site.hasPullbacks site.pretopology

end BigProetaleSite

end AlgebraicGeometry
