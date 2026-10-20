/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian

/-!
# Pseudo-catenary algebraic stacks

An algebraic stack is pseudo-catenary when it admits a surjective smooth atlas
from a universally catenary scheme. This is an existential atlas substitute for
the missing étale-local notion of a catenary stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is pseudo-catenary if it admits a surjective smooth atlas
from a universally catenary scheme. -/
@[mk_iff]
class IsPseudoCatenary {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop where
  /-- There is a surjective smooth 1-morphism from the slice of a universally
  catenary scheme. -/
  exists_universallyCatenary_smooth_cover :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.UniversallyCatenary U.left

namespace IsPseudoCatenary

/-- A pseudo-catenary algebraic stack admits a surjective smooth atlas from a
universally catenary scheme. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsPseudoCatenary X] :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.UniversallyCatenary U.left :=
  sorry

/-- A surjective smooth atlas from a universally catenary scheme witnesses that
the algebraic stack is pseudo-catenary. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p]
    [AlgebraicGeometry.UniversallyCatenary U.left] :
    IsPseudoCatenary X :=
  sorry

end IsPseudoCatenary

/-- The canonical slice of a universally catenary scheme over `S` is a
pseudo-catenary algebraic stack. -/
instance instIsPseudoCatenary_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.UniversallyCatenary U.left] :
    IsPseudoCatenary (GroupoidsOver.slice U) where
  exists_universallyCatenary_smooth_cover :=
    ⟨U, 𝟙 (GroupoidsOver.slice U), inferInstance, inferInstance, inferInstance⟩

/-- A pseudo-catenary algebraic stack is locally Noetherian. -/
instance instIsLocallyNoetherian {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [hX : IsPseudoCatenary X] : IsLocallyNoetherian X where
  exists_locallyNoetherian_smooth_cover :=
    Exists.elim hX.exists_universallyCatenary_smooth_cover fun U hU ↦
      Exists.elim hU fun p hp ↦
        ⟨U, p, hp.1, hp.2.1, hp.2.2.toIsLocallyNoetherian⟩

/-- An algebraic stack is pseudo-catenary if and only if it admits a surjective
smooth scheme atlas whose source is universally catenary. -/
theorem isPseudoCatenary_iff_existsSurjectiveSmooth {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsPseudoCatenary X ↔
      existsSurjectiveSmooth
        (AlgebraicGeometry.UniversallyCatenary : ObjectProperty Scheme.{u}) X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
