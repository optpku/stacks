/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenRestriction
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Open-cover descent data for locally ringed spaces

This leaf owns the compatibility and gluing predicates for contravariant set-valued functors on
locally ringed spaces. Canonical morphisms between nested restrictions live in `OpenRestriction`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace CategoryTheory.Functor

open AlgebraicGeometry

/-- A family of sections over opens `U j` is compatible when its two pullbacks to every pairwise
intersection agree. -/
@[stacks 01JK "open-cover compatibility on locally ringed spaces"]
def openCoverCompatible
    (F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v)
    {J : Type w} {X : LocallyRingedSpace.{u}}
    (U : J → Opens X)
    (s : ∀ j : J, F.obj (op (X.restrict (U j).isOpenEmbedding))) : Prop :=
  ∀ j k,
    F.map (LocallyRingedSpace.overlapToLeft (U j) (U k)).op (s j) =
      F.map (LocallyRingedSpace.overlapToRight (U j) (U k)).op (s k)

/-- A contravariant set-valued functor on locally ringed spaces satisfies open-cover gluing if
compatible sections on every open cover have a unique global amalgamation. -/
@[stacks 01JK "open-cover gluing on locally ringed spaces"]
def openCoverGluing (F : LocallyRingedSpace.{u}ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {J : Type w} ⦃X : LocallyRingedSpace.{u}⦄ (U : J → Opens X) (_ : IsOpenCover U)
    (s : ∀ j : J, F.obj (op (X.restrict (U j).isOpenEmbedding))),
      F.openCoverCompatible U s →
      ∃! t : F.obj (op X),
        ∀ j : J, F.map (X.ofRestrict (U j).isOpenEmbedding).op t = s j

end CategoryTheory.Functor
