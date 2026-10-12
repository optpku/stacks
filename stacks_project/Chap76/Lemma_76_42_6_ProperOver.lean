/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.«76_42_5_1_ProperSupport»

/-!
# Closed subsets proper over a morphism of algebraic spaces

A subset of `|X|` is proper over `f : X ⟶ Y` when it is contained in some
closed subspace whose structure morphism to `Y` is proper. This is the
set-level counterpart of `HasProperSupportOver`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A subset `T ⊆ |X|` is proper over `f : X ⟶ Y` when it is contained in some
closed subspace of `X` whose composite with `f` is proper. -/
class IsProperOver (f : X ⟶ Y) (T : Set (Points X)) : Prop where
  /-- Some closed subspace containing `T` is proper over `Y`. -/
  exists_closedSubspace :
    ∃ Z : ClosedSubspace X, Proper (Z.ι ≫ f) ∧ T ⊆ Z.pointsSet

/-- Properness of a subset over `f` is existence of a closed subspace containing
it whose composite with `f` is proper. -/
theorem isProperOver_iff (f : X ⟶ Y) (T : Set (Points X)) :
    IsProperOver f T ↔
      ∃ Z : ClosedSubspace X, Proper (Z.ι ≫ f) ∧ T ⊆ Z.pointsSet :=
  sorry

/-- A subset of a set proper over `f` is itself proper over `f`. -/
theorem isProperOver_mono {f : X ⟶ Y} {T T' : Set (Points X)} (hTT' : T ⊆ T')
    [IsProperOver f T'] : IsProperOver f T :=
  sorry

/-- If `f` is proper, then every subset of `|X|` is proper over `f`. -/
instance instIsProperOver_of_proper (f : X ⟶ Y) [Proper f] (T : Set (Points X)) :
    IsProperOver f T where
  exists_closedSubspace := ⟨ClosedSubspace.id X, sorry⟩

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A module has proper support over `f` if and only if its étale-site support
is proper over the target of `f`. -/
theorem hasProperSupportOver_iff_isProperOver (f : X ⟶ Y) (F : X.Modules) :
    HasProperSupportOver f F ↔ ClosedSubset.IsProperOver f (moduleSupport F) :=
  sorry

/-- The étale-site support of a module with proper support over `f` is proper
over the target of `f`. -/
instance instIsProperOver_of_hasProperSupportOver (f : X ⟶ Y) (F : X.Modules)
    [h : HasProperSupportOver f F] :
    ClosedSubset.IsProperOver f (moduleSupport F) where
  exists_closedSubspace := h.exists_closedSubspace

end AlgebraicGeometry.AlgebraicSpace.Modules
