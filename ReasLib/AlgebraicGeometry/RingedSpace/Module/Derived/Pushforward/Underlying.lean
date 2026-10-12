/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.UnderlyingPushforwardComparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
public import ReasLib.Topology.Sheaf.Derived.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying additive sheaves of derived pushforwards

This file specializes the generic ringed-site comparison between module pushforward and additive
sheaf pushforward.  It exposes the actual natural isomorphism and its objectwise components on the
ringed-space surface.
-/

@[expose] public section

-- Local instance justification (proof-local temporary data): source and target are mapDerivedCategory of the fixed underlying-additive-sheaf functor; its named additive and finite-limit/colimit proofs supply exactness without selecting a different functor.
attribute [local instance] AlgebraicGeometry.RingedSpace.moduleUnderlyingSheaf_additive
  AlgebraicGeometry.RingedSpace.moduleUnderlyingSheaf_preservesFiniteLimits
  AlgebraicGeometry.RingedSpace.moduleUnderlyingSheaf_preservesFiniteColimits


open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Underlying

variable {X Y : RingedSpace.{u}}

/-- Additive pushforward of sheaves along the underlying continuous map of a ringed-space
morphism. -/
@[stacks 0D5Y "underlying additive sheaf pushforward"]
abbrev functor (f : X ⟶ Y) :
    X.carrier.Sheaf AddCommGrpCat.{u} ⥤ Y.carrier.Sheaf AddCommGrpCat.{u} :=
  RingedSite.Hom.ModuleSections.additivePushforward (opensRingedSiteHom f)

/-- The total right-derived additive sheaf pushforward. -/
@[stacks 0D5Y "derived underlying additive sheaf pushforward"]
abbrev derivedFunctor (f : X ⟶ Y) :
    DerivedCategory (X.carrier.Sheaf AddCommGrpCat.{u}) ⥤
      DerivedCategory (Y.carrier.Sheaf AddCommGrpCat.{u}) :=
  RingedSite.Hom.ModuleSections.additivePushforwardDerived (opensRingedSiteHom f)

/-- Derived module pushforward followed by passage to the underlying additive sheaf. -/
@[stacks 0D5Y "underlying additive sheaf of derived module pushforward"]
abbrev source (f : X ⟶ Y) :
    ModuleDerived X ⥤ DerivedCategory (Y.carrier.Sheaf AddCommGrpCat.{u}) :=
  moduleDerivedPushforward f ⋙ (moduleUnderlyingSheaf Y).mapDerivedCategory

/-- Passage to the underlying additive sheaf followed by derived additive pushforward. -/
@[stacks 0D5Y "derived pushforward of the underlying additive sheaf"]
abbrev target (f : X ⟶ Y) :
    ModuleDerived X ⥤ DerivedCategory (Y.carrier.Sheaf AddCommGrpCat.{u}) :=
  (moduleUnderlyingSheaf X).mapDerivedCategory ⋙ derivedFunctor f

/-- Derived pushforward commutes canonically with passage to underlying additive sheaves. -/
@[stacks 0D5Y "derived pushforward underlying comparison"]
noncomputable def comparisonIso (f : X ⟶ Y) : source f ≅ target f :=
  RingedSite.Hom.ModuleSections.pushforwardIso (opensRingedSiteHom f)

/-- Objectwise underlying-additive comparison for derived pushforward. -/
@[stacks 0D5Y "derived pushforward underlying comparison component"]
noncomputable def appIso (f : X ⟶ Y) (K : ModuleDerived X) :
    (source f).obj K ≅ (target f).obj K :=
  (comparisonIso f).app K

end AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Underlying

end
