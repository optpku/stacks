/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map
public import ReasLib.CategoryTheory.Functor.Equivalence

/-!
# Symmetry of categorical pullbacks

The explicit swap functor, its quasi-inverse, and the associated projection comparison APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory
namespace Limits.CategoricalPullback

section CategoricalPullbackEquivalencesImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
/-! ### Two further congruences for the categorical pullback `⊡` -/

section CatPullbackMore

variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]

namespace Implementation

/-- The object obtained by reversing the two pullback legs. -/
private def swapObj (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    G ⊡ F where
  fst := x.snd
  snd := x.fst
  iso := x.iso.symm

/-- The morphism obtained by reversing its two pullback components. -/
private def swapMap (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : F ⊡ G} (f : x ⟶ y) :
    swapObj F G x ⟶ swapObj F G y where
  fst := f.snd
  snd := f.fst
  w := f.w'

/-- Reversing pullback components preserves identity morphisms. -/
private theorem swapMapId (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    swapMap F G (𝟙 x) = 𝟙 (swapObj F G x) := sorry
/- Proof strategy: apply `CategoricalPullback.hom_ext`; both exchanged components are identity
morphisms. -/

/-- Reversing pullback components preserves composition. -/
private theorem swapMapComp (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y z : F ⊡ G} (f : x ⟶ y) (g : y ⟶ z) :
    swapMap F G (f ≫ g) = swapMap F G f ≫ swapMap F G g := sorry
/- Proof strategy: apply `CategoricalPullback.hom_ext`; both exchanged components reduce to
composition in their source categories. -/

end Implementation

/-- Swap the two legs of a categorical pullback. -/
noncomputable def swap (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    F ⊡ G ⥤ G ⊡ F where
  obj := Implementation.swapObj F G
  map := Implementation.swapMap F G
  map_id := Implementation.swapMapId F G
  map_comp := Implementation.swapMapComp F G

/-- Swapping interchanges the two endpoint objects.

Proof strategy: project the left object of the explicit formula for `swap`. -/
@[simp]
theorem swap.obj.fst (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((swap F G).obj x).fst = x.snd := sorry

/-- Swapping interchanges the two endpoint objects.

Proof strategy: project the right object of the explicit formula for `swap`. -/
@[simp]
theorem swap.obj.snd (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((swap F G).obj x).snd = x.fst := sorry

/-- Swapping reverses the structural isomorphism.

Proof strategy: project the structural isomorphism of the explicit formula for `swap`. -/
@[simp]
theorem swap.obj.iso (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((swap F G).obj x).iso = x.iso.symm := sorry

/-- Swapping interchanges the two components of a morphism.

Proof strategy: project the left morphism component of the explicit formula for `swap`. -/
@[simp]
theorem swap.hom.fst (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : F ⊡ G} (f : x ⟶ y) :
    ((swap F G).map f).fst = f.snd := sorry

/-- Swapping interchanges the two components of a morphism.

Proof strategy: project the right morphism component of the explicit formula for `swap`. -/
@[simp]
theorem swap.hom.snd (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : F ⊡ G} (f : x ⟶ y) :
    ((swap F G).map f).snd = f.fst := sorry

namespace Implementation

/-- Coherence for the objectwise unit of the pullback-leg swap. -/
private theorem Swap.unitComponent_comm (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    F.map (𝟙 x.fst) ≫ ((swap F G ⋙ swap G F).obj x).iso.hom =
      x.iso.hom ≫ G.map (𝟙 x.snd) := sorry
/- Proof strategy: unfold both swaps; the double inverse of `x.iso` is `x.iso`, and the unit
morphisms disappear. -/

/-- Objectwise unit of the pullback-leg swap. -/
private noncomputable def Swap.unitComponent (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    x ≅ (swap F G ⋙ swap G F).obj x :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _)
    (Swap.unitComponent_comm F G x)

/-- Naturality of the objectwise unit of the pullback-leg swap. -/
private theorem Swap.unitNaturality (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : F ⊡ G} (f : x ⟶ y) :
    f ≫ (Swap.unitComponent F G y).hom =
      (Swap.unitComponent F G x).hom ≫
        (swap F G ⋙ swap G F).map f := sorry
/- Proof strategy: apply `CategoricalPullback.hom_ext`; each projection is an identity
composition. -/

/-- Unit natural isomorphism of the pullback-leg swap. -/
private noncomputable def Swap.unitIso (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    𝟭 (F ⊡ G) ≅ swap F G ⋙ swap G F :=
  NatIso.ofComponents (Swap.unitComponent F G)
    (Swap.unitNaturality F G)

end Implementation

/-- Explicit quasi-inverse data for the pullback-leg swap. -/
noncomputable def swap.quasiInverse (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    Functor.QuasiInverse (swap F G) where
  inverse := swap G F
  unitIso := Implementation.Swap.unitIso F G
  counitIso := (Implementation.Swap.unitIso G F).symm

/-- The inverse retained by the swap quasi-inverse data swaps the two legs back. -/
@[simp]
theorem swap.quasiInverse.inverse (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (swap.quasiInverse F G).inverse = swap G F := sorry

/-- The categorical pullback is invariant under swapping the two legs. -/
noncomputable def swap.equivalence (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    F ⊡ G ≌ G ⊡ F :=
  (swap.quasiInverse F G).adjointifyUnit

/-- The forward functor of the swap equivalence swaps the two legs.

Proof strategy: project the `functor` field of `swap.equivalence`. -/
@[simp]
theorem swap.equivalence.functor (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (swap.equivalence F G).functor = swap F G := sorry

/-- The inverse functor of the swap equivalence swaps the two legs back.

Proof strategy: project the `inverse` field of `swap.equivalence`. -/
@[simp]
theorem swap.equivalence.inverse (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (swap.equivalence F G).inverse = swap G F := sorry

/-- The counit of the swap equivalence is the explicitly specified reverse-swap unit. -/
@[simp]
theorem swap.equivalence.counitIso (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (swap.equivalence F G).counitIso =
      (swap.quasiInverse F G).counitIso := sorry

/-- The unit of the swap equivalence is the canonical adjointification of the specified swap
unit against its counit. -/
theorem swap.equivalence.unitIso (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (swap.equivalence F G).unitIso =
      Equivalence.adjointifyη
        (swap.quasiInverse F G).unitIso
          (swap.quasiInverse F G).counitIso := sorry

/-- The unit of the swap equivalence is the identity on the left component.

Proof strategy: project the explicit unit component through `CategoricalPullback.mkIso`. -/
@[simp]
theorem swap.equivalence.unitIso.hom.app.fst
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((swap.equivalence F G).unitIso.hom.app x).fst = 𝟙 x.fst := sorry

/-- The unit of the swap equivalence is the identity on the right component.

Proof strategy: project the explicit unit component through `CategoricalPullback.mkIso`. -/
@[simp]
theorem swap.equivalence.unitIso.hom.app.snd
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((swap.equivalence F G).unitIso.hom.app x).snd = 𝟙 x.snd := sorry

/-- The inverse component of the swap-equivalence unit is the identity on the left endpoint. -/
@[simp]
theorem swap.equivalence.unitIso.inv.app.fst
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((swap.equivalence F G).unitIso.inv.app x).fst = 𝟙 x.fst := sorry

/-- The inverse component of the swap-equivalence unit is the identity on the right endpoint. -/
@[simp]
theorem swap.equivalence.unitIso.inv.app.snd
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((swap.equivalence F G).unitIso.inv.app x).snd = 𝟙 x.snd := sorry

/-- The counit of the swap equivalence is the identity on the left component.

Proof strategy: project the inverse of the reverse-swap unit through
`CategoricalPullback.mkIso`. -/
@[simp]
theorem swap.equivalence.counitIso.hom.app.fst
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : G ⊡ F) :
    ((swap.equivalence F G).counitIso.hom.app x).fst = 𝟙 x.fst := sorry

/-- The counit of the swap equivalence is the identity on the right component.

Proof strategy: project the inverse of the reverse-swap unit through
`CategoricalPullback.mkIso`. -/
@[simp]
theorem swap.equivalence.counitIso.hom.app.snd
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : G ⊡ F) :
    ((swap.equivalence F G).counitIso.hom.app x).snd = 𝟙 x.snd := sorry

/-- The inverse component of the swap-equivalence counit is the identity on the left endpoint. -/
@[simp]
theorem swap.equivalence.counitIso.inv.app.fst
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : G ⊡ F) :
    ((swap.equivalence F G).counitIso.inv.app x).fst = 𝟙 x.fst := sorry

/-- The inverse component of the swap-equivalence counit is the identity on the right endpoint. -/
@[simp]
theorem swap.equivalence.counitIso.inv.app.snd
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : G ⊡ F) :
    ((swap.equivalence F G).counitIso.inv.app x).snd = 𝟙 x.snd := sorry

/-- The forward swap equivalence identifies the target first projection with the source second
projection. -/
noncomputable def swap.equivalence.functorFstIso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (swap.equivalence F G).functor ⋙ π₁ G F ≅
      π₂ F G :=
  Iso.refl _

/-- The forward swap equivalence identifies the target second projection with the source first
projection. -/
noncomputable def swap.equivalence.functorSndIso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (swap.equivalence F G).functor ⋙ π₂ G F ≅
      π₁ F G :=
  Iso.refl _

/-- The inverse swap equivalence identifies the source first projection with the target second
projection. -/
noncomputable def swap.equivalence.inverseFstIso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (swap.equivalence F G).inverse ⋙ π₁ F G ≅
      π₂ G F :=
  Iso.inverseCompIso (swap.equivalence.functorSndIso F G).symm

/-- The inverse swap equivalence identifies the source second projection with the target first
projection. -/
noncomputable def swap.equivalence.inverseSndIso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (swap.equivalence F G).inverse ⋙ π₂ F G ≅
      π₁ G F :=
  Iso.inverseCompIso (swap.equivalence.functorFstIso F G).symm

/-- Swapping the legs of a categorical pullback is an equivalence.

Proof strategy: transport the canonical instance on the forward functor of `swap.equivalence`. -/
instance swap.isEquivalence (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (swap F G).IsEquivalence := sorry

end CatPullbackMore

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback

end CategoryTheory
