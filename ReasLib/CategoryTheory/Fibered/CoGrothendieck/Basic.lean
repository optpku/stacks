module

-- Import decisions:
-- * The co-Grothendieck projection and `Grpd` are present in the public
--   object and morphism actions.
-- * The bundled fibred-in-groupoids target is part of those result types.
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Cartesian
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom

/-!
# Basic co-Grothendieck maps over a fixed base

The object and `1`-cell layers of the co-Grothendieck realization before they
are assembled into a pseudofunctor.
-/

@[expose] public section

universe w v₁ v₂ u

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open Opposite
open scoped Bicategory Pseudofunctor.StrongTrans

variable {𝒞 : Type u} [Category.{v₁} 𝒞]

/-- A co-Grothendieck projection whose pseudofunctor is pointwise groupoidal is canonically
fibred in groupoids. Strict `Grpd`-valued presheaves are a specialization below.

Mathlib's reindexed object and identity-fibre arrow supply each canonical Cartesian lift.
The explicit factor for every other arrow uses the inverse of its supplied fibre isomorphism;
the groupoid-fibre recognition theorem is not used as an existence factory. -/
instance forgetInGroupoids
    (F : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w})
    [∀ U, IsGroupoid (F.obj U)] :
    Functor.IsFibered.InGroupoids (forget F) where
  toIsFibered := Functor.IsFibered.of_exists_isStronglyCartesian
    (fun a _ f ↦
      ⟨domainCartesianLift a.fiber f, cartesianLift a.fiber f,
        isStronglyCartesian_homCartesianLift a.fiber f⟩)
  all_isCartesian := arrowIsCartesian F

/-- The category fibred in groupoids over `𝒞` represented by a pointwise groupoidal
pseudofunctor. This canonical owner-level construction is the object map of the co-Grothendieck
correspondence; it retains all object and morphism data from `F` through the canonical projection
`CoGrothendieck.forget F`. -/
def toFibered
    (F : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w})
    [∀ U, IsGroupoid (F.obj U)] :
    FiberedCategoryOver.Groupoids 𝒞 :=
  FiberedCategoryOver.Groupoids.ofFunctor (forget F)

/-- The projection of the bundled co-Grothendieck object is the canonical co-Grothendieck
projection. -/
@[simp]
theorem toFibered.p
    (F : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w})
    [∀ U, IsGroupoid (F.obj U)] :
    (toFibered F).p = forget F := sorry

/-- The functor induced by a strong transformation, bundled over the unchanged base. This is the
general based-category layer of the co-Grothendieck construction and does not require the fibers
to be groupoids. -/
def mapBased
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}} (α : F ⟶ G) :
    BasedCategory.ofFunctor (forget F) ⥤ᵇ
      BasedCategory.ofFunctor (forget G) :=
  BasedFunctor.ofFunctor (map α) (map_comp_forget α)

/-- A strong transformation of pointwise groupoidal pseudofunctors induces the canonical
`1`-morphism between their co-Grothendieck categories over the unchanged base.

The data are exactly `CoGrothendieck.map α`. Its base component is the identity because
`CoGrothendieck.map_comp_forget α` is definitional, so no additional comparison datum or
noncanonical choice is introduced. -/
def mapOver
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    [∀ U, IsGroupoid (F.obj U)] [∀ U, IsGroupoid (G.obj U)]
    (α : F ⟶ G) :
    toFibered F ⟶ toFibered G :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor (mapBased α)

/-- Forgetting the groupoid-fibred owner from `mapOver α` recovers the canonical based
co-Grothendieck map. -/
@[simp]
theorem mapOver.toBasedFunctor
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    [∀ U, IsGroupoid (F.obj U)] [∀ U, IsGroupoid (G.obj U)]
    (α : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (mapOver α) = mapBased α := sorry

/-- The total functor underlying `mapOver α` is the raw co-Grothendieck map. -/
@[simp]
theorem mapOver.toFunctor
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    [∀ U, IsGroupoid (F.obj U)] [∀ U, IsGroupoid (G.obj U)]
    (α : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toFunctor (mapOver α) = map α := sorry

/-- The co-Grothendieck map induced by a strong transformation commutes with the canonical
projections after both sides are bundled as categories fibred in groupoids. -/
theorem mapOver.comm
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    [∀ U, IsGroupoid (F.obj U)] [∀ U, IsGroupoid (G.obj U)]
    (α : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toFunctor (mapOver α) ⋙ (toFibered G).p =
      (toFibered F).p := sorry

/-- The co-Grothendieck object action preserves identity `1`-morphisms strictly after bundling
over the fixed base. This equality, rather than an additional comparison isomorphism, is the
canonical unity datum for the strict realization.

Proof strategy: apply `Bicategory.InducedBicategory.hom_ext`, then extensionality for based
functors. The underlying functor equality is `CoGrothendieck.map_id_eq F`; the base-compatibility
fields are propositions. -/
theorem mapOver.id
    (F : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w})
    [∀ U, IsGroupoid (F.obj U)] :
    mapOver (𝟙 F) = 𝟙 (toFibered F) := sorry

/-- The co-Grothendieck object action preserves horizontal composition strictly after bundling
over the fixed base. This is the equality form of `CoGrothendieck.map_comp_eq`.

Proof strategy: apply `Bicategory.InducedBicategory.hom_ext` and based-functor extensionality.
Use `CoGrothendieck.map_comp_eq α β` on the underlying functors; both base equations are
proof-irrelevant witnesses of the same strictly commuting projection square. -/
theorem mapOver.comp
    {F G H : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    [∀ U, IsGroupoid (F.obj U)] [∀ U, IsGroupoid (G.obj U)]
    [∀ U, IsGroupoid (H.obj U)]
    (α : F ⟶ G) (β : G ⟶ H) :
    mapOver (α ≫ β) = mapOver α ≫ mapOver β := sorry

end CategoryTheory.Pseudofunctor.CoGrothendieck
