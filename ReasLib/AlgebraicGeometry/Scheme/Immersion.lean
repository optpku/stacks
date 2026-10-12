/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedImmersion
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenImmersion

/-!
# Scheme immersions and their locally ringed-space views

Mathlib's scheme predicates remain the canonical owners. This module supplies
the closed-immersion forgetful bridges and the distinct open-then-closed factorization
property used by applications.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A scheme morphism is a closed immersion exactly when its locally ringed-space morphism is. -/
@[stacks 01IO "scheme closed immersion bridge"]
theorem isClosedImmersion_iff_toLRSHom_isClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsClosedImmersion f ↔ LocallyRingedSpace.IsClosedImmersion f.toLRSHom := sorry

/-- A scheme closed immersion remains a closed immersion after forgetting to locally ringed
spaces. -/
@[stacks 01IO "scheme closed immersion forgetful instance"]
instance Scheme.Hom.isClosedImmersion_toLRSHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    LocallyRingedSpace.IsClosedImmersion f.toLRSHom := sorry

/-- A locally ringed-space closed immersion underlying a scheme morphism is a scheme closed
immersion. -/
@[stacks 01IO "scheme closed immersion converse bridge"]
theorem Scheme.Hom.isClosedImmersion_of_toLRSHom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : LocallyRingedSpace.IsClosedImmersion f.toLRSHom) : IsClosedImmersion f := sorry

/-- The canonical closed-subscheme inclusion remains a closed immersion after forgetting to
locally ringed spaces. -/
@[stacks 01IO "closed subscheme forgetful bridge"]
theorem closedSubscheme_ι_toLRSHom_isClosedImmersion
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    LocallyRingedSpace.IsClosedImmersion I.subschemeι.toLRSHom := sorry

namespace Scheme.Hom

/-- The structure-sheaf map from a scheme to the pushforward of the source structure sheaf. -/
@[stacks 01LD "structure-sheaf map of a scheme morphism"]
noncomputable abbrev commRingSheafPushforwardMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  LocallyRingedSpace.Hom.commRingSheafPushforwardMap f.toLRSHom

/-- An immersion of schemes is closed exactly when its image is closed. -/
@[stacks 01IQ]
theorem isClosedImmersion_iff_isClosed_range_of_isImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    IsClosedImmersion f ↔ IsClosed (Set.range f) := sorry

end Scheme.Hom

namespace IsClosedImmersion

/-- A closed embedding with a locally surjective
structure-sheaf map is a closed immersion. -/
@[stacks 01LD]
theorem of_isClosedEmbedding_of_isLocallySurjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf_base : Topology.IsClosedEmbedding f)
    (hf_surj : Sheaf.IsLocallySurjective f.commRingSheafPushforwardMap) :
    IsClosedImmersion f := sorry

/-- A topological closed embedding together with surjectivity on all stalks is a closed
immersion. -/
@[stacks 01LD "closed immersion from closed embedding and stalk surjectivity"]
theorem of_isClosedEmbedding_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf_base : Topology.IsClosedEmbedding f)
    [SurjectiveOnStalks f] :
    IsClosedImmersion f := sorry

end IsClosedImmersion

/-- The morphism property of factoring as an open immersion followed by a closed immersion. -/
@[stacks 01IP "open immersion followed by closed immersion"]
abbrev IsOpenThenClosed : MorphismProperty Scheme.{u} :=
  MorphismProperty.comp IsOpenImmersion
    (fun {X Y} (f : X ⟶ Y) ↦ IsClosedImmersion f)

/-- Explicit factorization criterion for `IsOpenThenClosed`. -/
@[stacks 01IP "open-then-closed immersion factorization criterion"]
theorem isOpenThenClosed_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsOpenThenClosed f ↔
      ∃ (Z : Scheme.{u}) (openMap : X ⟶ Z) (closedMap : Z ⟶ Y),
        IsOpenImmersion openMap ∧ IsClosedImmersion closedMap ∧
          openMap ≫ closedMap = f := sorry

/-- Some immersion of schemes does not factor as an open immersion followed by a closed
immersion. -/
@[stacks 01IP]
theorem exists_isImmersion_not_isOpenThenClosed :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y), IsImmersion f ∧ ¬ IsOpenThenClosed f := sorry

end AlgebraicGeometry
