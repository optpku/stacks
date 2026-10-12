/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Category
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pushforward from an open subspace

This leaf owns direct image of module sheaves along the canonical open immersion. Exactness is
recorded at the underived level so that derived and homological constructions can reuse the same
instances without rebuilding them locally.
-/

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Direct image of `𝒪_U`-modules along the canonical open immersion `U ⟶ X`. -/
@[stacks 08DP "underived open-pushforward owner"]
abbrev modulePushforwardFromOpen (U : Opens X.carrier) :
    openSubspaceModuleCategory X U ⥤ X.Modules :=
  RingedSpace.Hom.pushforward (X.ofRestrict U.isOpenEmbedding)

namespace OpenSubspace.Pushforward

/-- Restriction to an open subspace is left adjoint to direct image from that subspace. -/
@[stacks 08DP "open restriction-pushforward adjunction"]
noncomputable def adjunction (X : RingedSpace.{u}) (U : Opens X.carrier) :
    moduleRestrictionToOpen X U ⊣ modulePushforwardFromOpen U :=
  RingedSpace.Hom.pullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)

/-- Restriction to an open subspace is a left adjoint. -/
instance isLeftAdjoint (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.IsLeftAdjoint (moduleRestrictionToOpen X U) := sorry

/-- Direct image from an open subspace is a right adjoint. -/
instance isRightAdjoint (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.IsRightAdjoint (modulePushforwardFromOpen U) := sorry

/-- The counit of restriction followed by direct image from an open subspace is an isomorphism. -/
instance counitIsIso (X : RingedSpace.{u}) (U : Opens X.carrier) :
    IsIso (adjunction X U).counit := sorry

/-- Every component of the restriction-pushforward counit is an isomorphism. -/
instance counitAppIsIso (X : RingedSpace.{u}) (U : Opens X.carrier)
    (F : openSubspaceModuleCategory X U) :
    IsIso ((adjunction X U).counit.app F) := sorry

/-- Direct image from an open subspace is fully faithful. -/
@[stacks 08DP "open pushforward is fully faithful"]
noncomputable def fullyFaithful (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).FullyFaithful :=
  (adjunction X U).fullyFaithfulROfIsIsoCounit

/-- Direct image from an open subspace is full. -/
noncomputable instance full (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).Full :=
  (fullyFaithful X U).full

/-- Direct image from an open subspace is faithful. -/
noncomputable instance faithful (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).Faithful :=
  (fullyFaithful X U).faithful

end OpenSubspace.Pushforward

/-- Direct image from an open subspace is additive. -/
instance OpenSubspace.Pushforward.additive (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).Additive := sorry

/-- Direct image from an open subspace is exact on module sheaves. -/
theorem OpenSubspace.Pushforward.isExact (U : Opens X.carrier) :
    exactFunctor (openSubspaceModuleCategory X U) X.Modules
      (modulePushforwardFromOpen U) := sorry

/-- Direct image from an open subspace preserves finite limits. -/
instance OpenSubspace.Pushforward.preservesFiniteLimits (U : Opens X.carrier) :
    PreservesFiniteLimits (modulePushforwardFromOpen U) := sorry

/-- Direct image from an open subspace preserves finite colimits. -/
instance OpenSubspace.Pushforward.preservesFiniteColimits (U : Opens X.carrier) :
    PreservesFiniteColimits (modulePushforwardFromOpen U) := sorry

end AlgebraicGeometry.RingedSpace
