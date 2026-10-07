module

public import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Birationality via Open Subschemes

This file characterizes birationality of irreducible schemes by isomorphic
nonempty open subschemes, both absolutely and over a base scheme.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- Two schemes have isomorphic nonempty open subschemes if each contains a nonempty open whose
associated scheme is isomorphic to that of the other. -/
def HasIsomorphicNonemptyOpenSubschemes (X Y : Scheme) : Prop :=
  ∃ U : X.Opens, ∃ V : Y.Opens,
    Nonempty U ∧ Nonempty V ∧ IsIsomorphic U.toScheme V.toScheme

/-- Two schemes over `S` have isomorphic nonempty open subschemes over `S` if their structure maps
restrict to isomorphic objects of `Over S` on some nonempty opens. -/
def HasIsomorphicNonemptyOpenSubschemesOver
    (S X Y : Scheme) [X.Over S] [Y.Over S] : Prop :=
  ∃ U : X.Opens, ∃ V : Y.Opens,
    Nonempty U ∧ Nonempty V ∧
      IsIsomorphic (Over.mk (U.ι ≫ (X ↘ S))) (Over.mk (V.ι ≫ (Y ↘ S)))

namespace Scheme

/-- Two irreducible schemes are birational if and only if they have isomorphic nonempty open
subschemes. -/
theorem birational_iff_hasIsomorphicNonemptyOpenSubschemes
    (X Y : Scheme) [IrreducibleSpace X] [IrreducibleSpace Y] :
    Scheme.Birational X Y ↔ HasIsomorphicNonemptyOpenSubschemes X Y := sorry

/-- Two irreducible schemes over `S` are birational over `S` if and only if they have nonempty open
subschemes that are isomorphic over `S`. -/
theorem birationalOver_iff_hasIsomorphicNonemptyOpenSubschemesOver
    (S X Y : Scheme) [X.Over S] [Y.Over S] [IrreducibleSpace X] [IrreducibleSpace Y] :
    Scheme.BirationalOver (X ↘ S) (Y ↘ S) ↔
      HasIsomorphicNonemptyOpenSubschemesOver S X Y := sorry

end Scheme

end AlgebraicGeometry
