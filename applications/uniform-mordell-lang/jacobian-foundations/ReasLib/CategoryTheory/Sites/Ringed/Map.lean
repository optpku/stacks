module

public import Mathlib.Algebra.Category.Ring.Basic
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

/-!
# Explicit maps of ringed sites

Ringed-site maps have contravariant base functors and adjoint structure-sheaf maps.
The sites and their ring sheaves are supplied explicitly.
-/

@[expose] public section

noncomputable section

universe uC vC uD vD uE vE w

namespace CategoryTheory

namespace RingedSiteMap

/-- Pushforward of ring sheaves along a functor with explicit site-morphism evidence. -/
def pushforward {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) (h : IsMorphismOfSites J K F) :
    Sheaf K RingCat.{w} ⥤ Sheaf J RingCat.{w} :=
  @Functor.sheafPushforwardContinuous _ _ _ _ F RingCat.{w} _ J K h.toIsContinuous

end RingedSiteMap

/-- A map of ringed sites consists of a contravariant site functor and an adjoint map
from the target ring sheaf to the pushforward of the source ring sheaf. -/
structure RingedSiteMap {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) (O : Sheaf J RingCat.{w})
    {D : Type uD} [Category.{vD} D]
    (K : GrothendieckTopology D) (P : Sheaf K RingCat.{w}) where
  base : D ⥤ C
  isMorphismOfSites : IsMorphismOfSites K J base := by infer_instance
  structureSheafMap : P ⟶ (RingedSiteMap.pushforward base isMorphismOfSites).obj O

namespace RingedSiteMap

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {J : GrothendieckTopology C} {O : Sheaf J RingCat.{w}}
  {K : GrothendieckTopology D} {P : Sheaf K RingCat.{w}}
  {L : GrothendieckTopology E} {Q : Sheaf L RingCat.{w}}

/-- The identity ringed-site map has identity base functor and identity sheaf map. -/
def id (J : GrothendieckTopology C) (O : Sheaf J RingCat.{w}) : RingedSiteMap J O J O where
  base := 𝟭 C
  isMorphismOfSites := IsMorphismOfSites.id J
  structureSheafMap := 𝟙 O

/-- Composition of ringed-site maps composes base functors contravariantly and sheaf maps
in adjoint pushforward form. -/
def comp (f : RingedSiteMap J O K P) (g : RingedSiteMap K P L Q) :
    RingedSiteMap J O L Q where
  base := g.base ⋙ f.base
  isMorphismOfSites :=
    @IsMorphismOfSites.comp _ _ _ _ _ _ _ K _ g.base f.base
      g.isMorphismOfSites f.isMorphismOfSites
  structureSheafMap :=
    g.structureSheafMap ≫
      (pushforward g.base g.isMorphismOfSites).map f.structureSheafMap

/-- The identity ringed-site map has the identity base functor. -/
@[simp]
theorem id_base (J : GrothendieckTopology C) (O : Sheaf J RingCat.{w}) :
    (id J O).base = 𝟭 C := rfl

/-- The base functor of a composite is the reverse composite of the base functors. -/
@[simp]
theorem comp_base (f : RingedSiteMap J O K P) (g : RingedSiteMap K P L Q) :
    (comp f g).base = g.base ⋙ f.base := rfl

/-- An isomorphism of ringed sites is a pair of explicit maps satisfying both inverse laws. -/
structure Iso (J : GrothendieckTopology C) (O : Sheaf J RingCat.{w})
    (K : GrothendieckTopology D) (P : Sheaf K RingCat.{w}) where
  hom : RingedSiteMap J O K P
  inv : RingedSiteMap K P J O
  hom_inv_id : comp hom inv = id J O
  inv_hom_id : comp inv hom = id K P

/-- Reversing a ringed-site isomorphism swaps its maps and inverse laws. -/
def Iso.symm (e : Iso J O K P) : Iso K P J O where
  hom := e.inv
  inv := e.hom
  hom_inv_id := e.inv_hom_id
  inv_hom_id := e.hom_inv_id

end RingedSiteMap

end CategoryTheory
