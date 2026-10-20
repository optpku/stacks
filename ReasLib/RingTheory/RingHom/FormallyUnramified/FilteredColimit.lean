module

public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Formal unramifiedness and filtered colimits

This leaf makes formal unramifiedness available to the generic filtered-
colimit machinery for morphism properties, then exposes direct `Under`
category interfaces for a chosen colimit cocone and the canonical colimit.

@stack 07QE
-/

@[expose] public section

open CategoryTheory MorphismProperty Limits
open CategoryTheory.Under
open CommRingCat
open CommRingCat.Hom

universe u v

namespace RingHom.FormallyUnramified

/-- Formal unramifiedness is stable under filtered colimits of commutative
ring morphisms. -/
@[stacks 07QE "formal unramified filtered-colimit closure"]
instance isStableUnderFilteredColimits :
    MorphismProperty.IsStableUnderFilteredColimits
      (fun {A B : CommRingCat} (f : A ⟶ B) ↦ (hom f).FormallyUnramified) := sorry

/-- Stacks tag `07QE`: a colimit of a filtered system of formally unramified
commutative algebras over `R` is formally unramified over `R`. -/
@[stacks 07QE "formal unramified filtered-colimit closure"]
theorem of_isColimit
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FormallyUnramified) :
    (hom c.pt.hom).FormallyUnramified := sorry

/-- The canonical colimit form of `of_isColimit`. -/
@[stacks 07QE "formal unramified filtered-colimit closure"]
theorem of_colimit
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R)) [HasColimit F]
    (hF : ∀ j, (hom (F.obj j).hom).FormallyUnramified) :
    (hom (colimit F).hom).FormallyUnramified := sorry

end RingHom.FormallyUnramified
