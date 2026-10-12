/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived sections over inverse-image opens

This file specializes the generic ringed-site direct-image comparison to an open subset of a
ringed space.  The comparison is exposed as an actual natural isomorphism, so downstream code can
use its components and naturality without choosing an `IsIsomorphic` witness.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Preimage

variable {X Y : RingedSpace.{u}}

/-- Derived sections on `f ⁻¹ᵁ V`, with scalars restricted along
`Γ(V, 𝒪_Y) ⟶ Γ(f ⁻¹ᵁ V, 𝒪_X)`. -/
@[stacks 0D5W "derived sections over an inverse-image open"]
abbrev functor (f : X ⟶ Y) (V : Opens Y.carrier) :
    ModuleDerived X ⥤ DerivedCategory (ModuleCat (sectionsRingOnOpen Y V)) :=
  moduleDerivedSectionsAtOpen X (preimageOpen f V) ⋙
    moduleSectionsRestrictionDerived f V

/-- The canonical opens-ringed-site source for derived sections over an inverse-image open. -/
@[stacks 0D5W "canonical derived sections source over an inverse-image open"]
abbrev canonicalSource (f : X ⟶ Y) (V : Opens Y.carrier) :=
  RingedSite.Hom.ModuleSections.objectSourceDerived (opensRingedSiteHom f) V

/-- The canonical opens-ringed-site target for derived pushforward followed by sections. -/
@[stacks 0D5W "canonical derived pushforward sections target"]
abbrev canonicalTarget (f : X ⟶ Y) (V : Opens Y.carrier) :=
  RingedSite.Hom.ModuleSections.objectTargetDerived (opensRingedSiteHom f) V

/-- The concrete generic comparison between the canonical opens-ringed-site models. -/
@[stacks 0D5W "canonical derived sections and pushforward comparison"]
noncomputable def comparisonIso (f : X ⟶ Y) (V : Opens Y.carrier) :
    canonicalSource f V ≅ canonicalTarget f V :=
  RingedSite.Hom.ModuleSections.objectPushforwardComparisonIso
    (opensRingedSiteHom f) V

/-- Derived sections over an inverse-image open, in the cochain-derived model used by the
ringed-space API, are isomorphic to derived pushforward followed by derived sections on the
target open. -/
@[stacks 0D5W "derived sections over an inverse image and derived pushforward"]
theorem isomorphic (f : X ⟶ Y) (V : Opens Y.carrier) :
    IsIsomorphic (functor f V)
      (moduleDerivedPushforward f ⋙ moduleDerivedSectionsAtOpen Y V) := sorry

/-- Objectwise form of the inverse-image-open derived-sections comparison. -/
@[stacks 0D5W "objectwise derived sections over an inverse image"]
theorem obj_isomorphic (f : X ⟶ Y) (V : Opens Y.carrier) (K : ModuleDerived X) :
    IsIsomorphic ((functor f V).obj K)
      ((moduleDerivedSectionsAtOpen Y V).obj ((moduleDerivedPushforward f).obj K)) := sorry

end AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Preimage

end
