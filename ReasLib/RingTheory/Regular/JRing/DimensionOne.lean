/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.Regular.JRing
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# One-Dimensional J-2 Rings

@stack 07PJ

The reusable statements use mathlib's `Ring.KrullDimLE 1` owner. The equality-based companions
retain the textbook formulation without installing a dimension equality as an instance.
-/

universe u v

namespace IsJ2Ring

/-- A Noetherian local ring of Krull dimension at most one is `J-2`. -/
@[stacks 07PJ "(4), local rings of dimension at most one"]
theorem of_localRing_krullDimLEOne
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] : IsJ2Ring.{u, v} R := sorry

/-- A Noetherian local ring of Krull dimension one is `J-2`. -/
@[stacks 07PJ "(4), one-dimensional local rings"]
theorem of_localRing_dimensionOne
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h_dimension : ringKrullDim R = 1) : IsJ2Ring.{u, v} R := sorry

/-- A Nagata ring of Krull dimension at most one is `J-2`. -/
@[stacks 07PJ "(5), Nagata rings of dimension at most one"]
theorem of_nagataRing_krullDimLEOne
    (R : Type u) [CommRing R] [NagataRing R] [Ring.KrullDimLE 1 R] :
    IsJ2Ring.{u, v} R := sorry

/-- A Nagata ring of Krull dimension one is `J-2`. -/
@[stacks 07PJ "(5), one-dimensional Nagata rings"]
theorem of_nagataRing_dimensionOne
    (R : Type u) [CommRing R] [NagataRing R]
    (h_dimension : ringKrullDim R = 1) : IsJ2Ring.{u, v} R := sorry

end IsJ2Ring
