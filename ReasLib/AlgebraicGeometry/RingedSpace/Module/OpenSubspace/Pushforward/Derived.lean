module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived pushforward from an open subspace

The derived direct image is obtained from the exact underived open-pushforward functor. All
exactness and derived-category instances are supplied by the owner leaves imported above.
-/

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The derived direct-image functor `Rj_* : D(𝒪_U) ⥤ D(𝒪_X)` for the canonical open
immersion `j : U ⟶ X`. -/
@[stacks 08DP "derived open-pushforward owner"]
noncomputable abbrev modulePushforwardFromOpenDerived (U : Opens X.carrier) :
    moduleDerivedOnOpen X U ⥤ ModuleDerived X :=
  (modulePushforwardFromOpen U).mapDerivedCategory

namespace OpenSubspace.Pushforward

/-- The adjunction `j^* ⊣ Rj_*` for an open subspace on unbounded derived categories. -/
@[stacks 08DP "derived open restriction-pushforward adjunction"]
noncomputable def derivedAdjunction (X : RingedSpace.{u}) (U : Opens X.carrier) :
    moduleRestrictionToOpenDerived X U ⊣ modulePushforwardFromOpenDerived U :=
  CategoryTheory.Adjunction.mapDerivedCategory (adjunction X U)

/-- Derived restriction to an open subspace is a left adjoint. -/
instance derivedIsLeftAdjoint (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.IsLeftAdjoint (moduleRestrictionToOpenDerived X U) := sorry

/-- Derived direct image from an open subspace is a right adjoint. -/
instance derivedIsRightAdjoint (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.IsRightAdjoint (modulePushforwardFromOpenDerived U) := sorry

/-- The counit of the derived restriction-pushforward adjunction is an isomorphism. -/
instance derivedCounitIsIso (X : RingedSpace.{u}) (U : Opens X.carrier) :
    IsIso (derivedAdjunction X U).counit := sorry

/-- Every component of the derived restriction-pushforward counit is an isomorphism. -/
@[stacks 08DP "derived open restriction-pushforward counit component"]
instance derivedCounitAppIsIso (X : RingedSpace.{u}) (U : Opens X.carrier)
    (F : moduleDerivedOnOpen X U) :
    IsIso ((derivedAdjunction X U).counit.app F) := sorry

/-- Derived direct image from an open subspace is fully faithful. -/
@[stacks 08DP "derived open pushforward is fully faithful"]
noncomputable def derivedFullyFaithful (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (modulePushforwardFromOpenDerived U).FullyFaithful :=
  (derivedAdjunction X U).fullyFaithfulROfIsIsoCounit

/-- Derived direct image from an open subspace is full. -/
noncomputable instance derivedFull (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (modulePushforwardFromOpenDerived U).Full :=
  (derivedFullyFaithful X U).full

/-- Derived direct image from an open subspace is faithful. -/
noncomputable instance derivedFaithful (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (modulePushforwardFromOpenDerived U).Faithful :=
  (derivedFullyFaithful X U).faithful

end OpenSubspace.Pushforward

end AlgebraicGeometry.RingedSpace
