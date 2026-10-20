/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Functor
public import ReasLib.AlgebraicGeometry.RelativeCycle.Reduction
public import stacks_project.Chap62.Definition_62_6_1_Specialization

/-!
# Effective-cycle transport compatibility

The mathematical constructions are provided by their shared owners. The
source-level family spellings and the two compatibility abbreviations preserve
the directed inverse-limit construction's existing interface.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

#check (AlgebraicGeometry.RelativeCycle.familyMapOfIsoOver :
  ∀ {X X' S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {f' : X' ⟶ S} [LocallyOfFiniteType f']
    (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (r : ℕ),
    f.FiberCycleFamily r →+ f'.FiberCycleFamily r)

/-- Compatibility spelling for closed-immersion pushforward along an isomorphism. -/
abbrev groupMapOfIsoOver {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (r : ℕ) :
    group f r →+ group f' r :=
  groupPushforward f f' e w r

/-- Compatibility spelling for the canonical nested pullback isomorphism. -/
abbrev pullbackSndAssocIso {X S S' S'' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (h : S'' ⟶ S') :
    pullback (pullback.snd f g) h ≅ pullback f (h ≫ g) :=
  pullbackLeftPullbackSndIso f g h

namespace InverseLimit

/-- Isomorphism transport of fibrewise cycle families, deriving local finite type
of the target morphism from the commuting triangle. -/
def familyMapOfIsoOver {X X' S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {f' : X' ⟶ S} (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (r : ℕ) :
    -- Local instance justification (defeq pin): The legacy dependent result needs LocallyOfFiniteType f' derived from this isomorphic triangle before FiberCycleFamily f' can elaborate, without installing a global inference rule.
    letI : LocallyOfFiniteType f' :=
      (MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFiniteType) e f').mp
        (w.symm ▸ ‹LocallyOfFiniteType f›)
    f.FiberCycleFamily r →+ f'.FiberCycleFamily r := by
  -- Local instance justification (defeq pin): Repeat the result-type finite-type derivation so the canonical transport elaborates at the same dependent target without a global inference rule.
  letI : LocallyOfFiniteType f' :=
    (MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFiniteType) e f').mp
      (w.symm ▸ ‹LocallyOfFiniteType f›)
  exact AlgebraicGeometry.RelativeCycle.familyMapOfIsoOver e w r

end InverseLimit

end AlgebraicGeometry.RelativeCycle
