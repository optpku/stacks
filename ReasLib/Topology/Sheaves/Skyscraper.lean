/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Skyscraper sheaves

Mathlib owns the underlying decidable construction. This module exposes the project-facing
classical wrappers and stalk interfaces, so point-open decidability is not part of downstream
mathematical APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u v

namespace TopCat.Sheaf.Skyscraper

/-- The canonical skyscraper sheaf at `x` with value `A`, using classical decidability of open
membership internally. This is the project-facing construction when a decidability instance is
not mathematical input. -/
noncomputable abbrev atPoint {X : TopCat.{u}} {C : Type v} [Category.{u} C] [HasTerminal C]
    (x : X) (A : C) : TopCat.Sheaf C X :=
  @skyscraperSheaf X x (fun _ ↦ Classical.dec _) C _ A _

/-- Sending `A` to the classical skyscraper sheaf `atPoint x A`. -/
noncomputable abbrev functor {X : TopCat.{u}} {C : Type v} [Category.{u} C] [HasTerminal C]
    (x : X) : C ⥤ TopCat.Sheaf C X :=
  @skyscraperSheafFunctor X x (fun _ ↦ Classical.dec _) C _ _

/-- The stalk functor at `x` is left adjoint to the classical skyscraper functor. -/
noncomputable abbrev stalkAdjunction {X : TopCat.{u}} {C : Type v} [Category.{u} C]
    [HasTerminal C] [HasColimits C] (x : X) :
    TopCat.Sheaf.forget C X ⋙ TopCat.Presheaf.stalkFunctor C x ⊣ functor x :=
  @stalkSkyscraperSheafAdjunction X x (fun _ ↦ Classical.dec _) C _ _ _

/-- The presheaf stalk functor is left adjoint to the underlying presheaf of the classical
skyscraper sheaf. -/
noncomputable abbrev presheafStalkAdjunction
    {X : TopCat.{u}} {C : Type v} [Category.{u} C]
    [HasTerminal C] [HasColimits C] (x : X) :
    TopCat.Presheaf.stalkFunctor C x ⊣ functor x ⋙ TopCat.Sheaf.forget C X :=
  @skyscraperSheafForgetAdjunction X x (fun _ ↦ Classical.dec _) C _ _ _

/-- The classical skyscraper presheaf underlying `atPoint` is the pushforward from the one-point
space. -/
theorem presheaf_eq_pushforward {X : TopCat.{u}} {C : Type v} [Category.{u} C] [HasTerminal C]
    (x : X) (A : C) :
    (atPoint x A).presheaf =
      (ofHom (ContinuousMap.const (TopCat.of PUnit) x)) _*
        (atPoint (X := TopCat.of PUnit) PUnit.unit A).presheaf := sorry

/-- At a specialization of its support point, the stalk of `atPoint x A` is canonically `A`. -/
noncomputable def stalkIsoOfSpecializes {X : TopCat.{u}} (x : X) {C : Type v} [Category.{u} C]
    [HasTerminal C] [HasColimits C] (A : C) {x' : X} (h : x ⤳ x') :
    (atPoint x A).presheaf.stalk x' ≅ A :=
  @skyscraperPresheafStalkOfSpecializes X x (fun _ ↦ Classical.dec _) C _ A _ _ x' h

/-- Away from the specializations of its support point, the stalk of `atPoint x A` is terminal. -/
noncomputable def stalkIsoOfNotSpecializes {X : TopCat.{u}} (x : X) {C : Type v}
    [Category.{u} C] [HasTerminal C] [HasColimits C] (A : C) {x' : X} (h : ¬x ⤳ x') :
    (atPoint x A).presheaf.stalk x' ≅ terminal C :=
  @skyscraperPresheafStalkOfNotSpecializes X x (fun _ ↦ Classical.dec _) C _ A _ _ x' h

end TopCat.Sheaf.Skyscraper

namespace TopCat.Sheaf

/-- A sheaf is skyscraper when it is isomorphic to `Skyscraper.atPoint x A` for some point `x`
and value `A`. -/
def IsSkyscraper {X : TopCat.{u}} {C : Type v} [Category C] [Limits.HasTerminal C]
    (ℱ : TopCat.Sheaf C X) : Prop :=
  ∃ (x : X) (A : C), IsIsomorphic ℱ (TopCat.Sheaf.Skyscraper.atPoint x A)

end TopCat.Sheaf
