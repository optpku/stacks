module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Pretopology
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Map
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Tautological

/-!
# Chosen presentations of big scheme sites

A chosen presentation records a small category of schemes, selected objects and
covering families, and a pretopology whose coverings are represented by covers
for a fixed precoverage on schemes.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- The laws relating selected objects and covering families in a small category
of schemes to a precoverage on schemes. -/
structure IsChosenBigSite (P : Precoverage Scheme.{u}) (carrier : Cat.{v, u})
    (hasPullbacks : Limits.HasPullbacks carrier) (toScheme : Functor carrier Scheme.{u})
    (seedSchemes : Set carrier) (seedCoverings : ∀ X : carrier, Set (Presieve X))
    (pretopology : @Pretopology carrier (Cat.str carrier) hasPullbacks) : Prop where
  /-- The functor to schemes preserves pullbacks. -/
  toScheme_preservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan toScheme
  /-- The target of every selected covering family is selected. -/
  seedCovering_target_mem :
    ∀ {X : carrier} {R : Presieve X}, R ∈ seedCoverings X → X ∈ seedSchemes
  /-- The source of every arrow in a selected covering family is selected. -/
  seedCovering_source_mem :
    ∀ {X : carrier} {R : Presieve X}, R ∈ seedCoverings X →
      ∀ {Y : carrier} (f : Y ⟶ X), R f → Y ∈ seedSchemes
  /-- Every selected covering family belongs to the pretopology. -/
  seedCoverings_le :
    ∀ {X : carrier} {R : Presieve X}, R ∈ seedCoverings X → R ∈ pretopology X
  /-- Every selected covering family is represented, after applying the scheme
functor, by a cover for the ambient precoverage. -/
  seedCovering_exists_cover :
    ∀ {X : carrier} {R : Presieve X}, R ∈ seedCoverings X →
      ∃ 𝒰 : Scheme.Cover.{u} P (toScheme.obj X),
        R.map toScheme = Presieve.ofArrows 𝒰.X 𝒰.f
  /-- Every covering family in the pretopology is represented, after applying
the scheme functor, by a cover for the ambient precoverage. -/
  covering_exists_cover :
    ∀ {X : carrier} {R : Presieve X}, R ∈ pretopology X →
      ∃ 𝒰 : Scheme.Cover.{u} P (toScheme.obj X),
        R.map toScheme = Presieve.ofArrows 𝒰.X 𝒰.f
  /-- Every source in an ambient cover is isomorphic to the image of an object
  in the chosen carrier. -/
  coverSource_exists_iso :
    ∀ {X : carrier} (𝒰 : Scheme.Cover.{u} P (toScheme.obj X)) (i : 𝒰.I₀),
      ∃ Y : carrier, Nonempty (toScheme.obj Y ≅ 𝒰.X i)
  /-- A family in the chosen carrier covers whenever its image is
  tautologically equivalent to an ambient cover. -/
  isCovering_of_tautologicallyEquivalent :
    ∀ {X : carrier} (𝒰 : Scheme.Cover.{u} P (toScheme.obj X))
      (𝒱 : Limits.FormalCoproduct.{u} (CategoryTheory.Over X)),
      Limits.FormalCoproduct.TautologicallyEquivalent
          ((Limits.FormalCoproduct.map
            (CategoryTheory.Over.post (X := X) toScheme)).obj 𝒱)
          (Limits.FormalCoproduct.Over.ofArrows 𝒰.X 𝒰.f) →
        Limits.FormalCoproduct.Over.IsCovering pretopology.toPrecoverage 𝒱

/-- An explicit small presentation of a big site associated to a precoverage on
schemes. -/
structure ChosenBigSite (P : Precoverage Scheme.{u}) where
  /-- The selected small category. -/
  carrier : Cat.{v, u}
  /-- A proof that the selected category has pullbacks. -/
  hasPullbacks : Limits.HasPullbacks carrier
  /-- The functor exhibiting the selected category as a category of schemes. -/
  toScheme : Functor carrier Scheme.{u}
  /-- The scheme functor is fully faithful. -/
  fullyFaithful : toScheme.FullyFaithful
  /-- The selected objects of the presentation. -/
  seedSchemes : Set carrier
  /-- The selected covering families of the presentation. -/
  seedCoverings : ∀ X : carrier, Set (Presieve X)
  /-- The pretopology on the selected category. -/
  pretopology : @Pretopology carrier (Cat.str carrier) hasPullbacks
  /-- The selected objects, covering families, and pretopology represent the
ambient scheme precoverage. -/
  specification :
    IsChosenBigSite P carrier hasPullbacks toScheme seedSchemes seedCoverings pretopology

namespace ChosenBigSite

variable {P : Precoverage Scheme.{u}}

/-- Construct a chosen big-site presentation from explicit carrier, functor,
seed, pretopology, and specification data. -/
def ofPretopology (carrier : Cat.{v, u}) (hasPullbacks : Limits.HasPullbacks carrier)
    (toScheme : Functor carrier Scheme.{u}) (fullyFaithful : toScheme.FullyFaithful)
    (seedSchemes : Set carrier) (seedCoverings : ∀ X : carrier, Set (Presieve X))
    (pretopology : @Pretopology carrier (Cat.str carrier) hasPullbacks)
    (specification :
      IsChosenBigSite P carrier hasPullbacks toScheme seedSchemes seedCoverings pretopology) :
    ChosenBigSite P where
  carrier := carrier
  hasPullbacks := hasPullbacks
  toScheme := toScheme
  fullyFaithful := fullyFaithful
  seedSchemes := seedSchemes
  seedCoverings := seedCoverings
  pretopology := pretopology
  specification := specification

/-- The complete specification satisfied by a chosen big-site presentation. -/
theorem spec (X : ChosenBigSite P) :
    IsChosenBigSite P X.carrier X.hasPullbacks X.toScheme X.seedSchemes
      X.seedCoverings X.pretopology :=
  X.specification

/-- The Grothendieck topology generated by the pretopology of a chosen
big-site presentation. -/
def toGrothendieck (X : ChosenBigSite P) : GrothendieckTopology X.carrier :=
  @Pretopology.toGrothendieck X.carrier (Cat.str X.carrier) X.hasPullbacks X.pretopology

end ChosenBigSite

/-- An explicit small presentation of a big Zariski site. -/
abbrev ChosenBigZariskiSite : Type (max (u + 1) (v + 1)) :=
  ChosenBigSite.{u, v} Scheme.zariskiPrecoverage

end AlgebraicGeometry
