/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.LeftIdentity.Basic

/-!
# The left-identity categorical-pullback equivalence

This leaf assembles the explicit inverse to `π₂ (𝟙 C) G` with explicit unit and counit
natural isomorphisms.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory.Limits.CategoricalPullback.LeftIdentity

universe vB vC uB uC

variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable (G : B ⥤ C)

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EquivalenceImplementation

/-- Compatibility of the two components of the left-identity unit at a pullback object. -/
private theorem unitComponentComm (x : (Functor.id C) ⊡ G) :
    (Functor.id C).map x.iso.hom ≫
        ((π₂ (Functor.id C) G ⋙ inverse G).obj x).iso.hom =
      x.iso.hom ≫ G.map (𝟙 x.snd) := sorry

/-- The left-identity unit component uses the pullback object's structural isomorphism on its
first coordinate and the identity on its second coordinate. -/
private def unitComponent (x : (Functor.id C) ⊡ G) :
    x ≅ (π₂ (Functor.id C) G ⋙ inverse G).obj x :=
  CategoricalPullback.mkIso x.iso (Iso.refl _)
    (unitComponentComm G x)

/-- Naturality of the explicit left-identity unit components. -/
private theorem unitNaturality {x y : (Functor.id C) ⊡ G} (f : x ⟶ y) :
    f ≫ (unitComponent G y).hom =
      (unitComponent G x).hom ≫
        (π₂ (Functor.id C) G ⋙ inverse G).map f := sorry

/-- The explicit unit for the left-identity categorical-pullback equivalence. -/
private def unitIso :
    Functor.id ((Functor.id C) ⊡ G) ≅
      π₂ (Functor.id C) G ⋙ inverse G :=
  NatIso.ofComponents (unitComponent G) (unitNaturality G)

/-- Naturality of the identity counit components for the left-identity comparison. -/
private theorem counitNaturality {x y : B} (f : x ⟶ y) :
    (inverse G ⋙ π₂ (Functor.id C) G).map f ≫ (Iso.refl y).hom =
      (Iso.refl x).hom ≫ f := sorry

/-- The explicit identity counit for the left-identity categorical-pullback equivalence. -/
private def counitIso :
    inverse G ⋙ π₂ (Functor.id C) G ≅ Functor.id B :=
  NatIso.ofComponents (fun x ↦ Iso.refl x)
    (fun f ↦ counitNaturality G f)

/-- Triangle coherence for the explicit left-identity unit and counit. -/
private theorem triangle (x : (Functor.id C) ⊡ G) :
    (π₂ (Functor.id C) G).map ((unitIso G).hom.app x) ≫
        (counitIso G).hom.app ((π₂ (Functor.id C) G).obj x) =
      𝟙 ((π₂ (Functor.id C) G).obj x) := sorry

end EquivalenceImplementation

/-- The canonical equivalence from the categorical pullback along an identity functor to its
right-hand category.  Its forward functor is the existing projection `π₂ (𝟙 C) G`, and its
inverse, unit, and counit data are explicit. -/
def equivalence : ((Functor.id C) ⊡ G) ≌ B where
  functor := π₂ (Functor.id C) G
  inverse := LeftIdentity.inverse G
  unitIso := EquivalenceImplementation.unitIso G
  counitIso := EquivalenceImplementation.counitIso G
  functor_unitIso_comp := EquivalenceImplementation.triangle G

end CategoryTheory.Limits.CategoricalPullback.LeftIdentity
