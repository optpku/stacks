/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
public import ReasLib.CategoryTheory.Sites.TopologyComparison.AbsoluteDerived
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Comparison of the big fppf and h topologies

This module records the topology inclusion and the existence of the associated
unbounded right-derived direct image.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Derived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.H

/-- Every big fppf covering sieve over `S` is a covering sieve for the big h topology. -/
theorem fppf_le (S : Scheme.{u}) :
    Scheme.fppfTopology.over S ≤ (Scheme.hPrecoverage.toGrothendieck).over S :=
  sorry

/-- The h-to-fppf direct image admits its canonical unbounded right-derived functor. -/
instance hasRightDerivedPushforward (S : Scheme.{u}) :
    Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived
        (Absolute.pushforward (fppf_le S)))
      (Absolute.qis ((Scheme.hPrecoverage.toGrothendieck).over S)) :=
  sorry

end AlgebraicGeometry.Scheme.H

end
