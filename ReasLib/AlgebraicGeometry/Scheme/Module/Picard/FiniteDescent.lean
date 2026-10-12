/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Constructions
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.ClosedImmersion

/-!
# Finite descent of invertible modules

This leaf supplies the invertible-module descent statement for a finite scheme
morphism that is an isomorphism away from a discrete complement.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteDescent

variable {X Y : Scheme.{u}}

/-- If a finite morphism is an isomorphism over an open subset with discrete
complement, then every invertible module on the source is the pullback of an
invertible module on the target. -/
@[stacks 0C0T]
theorem existsInvertiblePullback
    (f : X ⟶ Y) [IsFinite f]
    (h_open : ∃ (V : Y.Opens) (_ : IsIso (f ∣_ V)), IsDiscrete ((V : Set Y)ᶜ))
    (L : X.Modules) [Modules.Invertible L] :
    ∃ (N : Y.Modules) (_ : Modules.Invertible N),
      Nonempty (L ≅ ((Scheme.Modules.pullback f).obj N)) := sorry

/-- Every invertible module descends along a finite morphism to a Noetherian
scheme of dimension at most one when its restriction to some dense open is a
closed immersion. -/
@[stacks 0C0U]
theorem existsInvertiblePullback_of_exists_dense_open_isClosedImmersion
    (f : X ⟶ Y) [IsFinite f] [IsNoetherian Y]
    (hdim : topologicalKrullDim Y ≤ 1)
    (hV : ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsClosedImmersion (f ∣_ V))
    (L : X.Modules) [Modules.Invertible L] :
    ∃ (N : Y.Modules) (_ : Modules.Invertible N),
      Nonempty (L ≅ (Scheme.Modules.pullback f).obj N) := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteDescent
