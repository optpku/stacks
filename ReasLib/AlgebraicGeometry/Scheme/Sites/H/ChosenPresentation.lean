/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation

/-!
# Slice topologies of chosen big h sites

This module defines the topology induced on a slice of a chosen presentation
of the big h site.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigHSite

/-- The big h topology over a represented base is the slice topology of the
chosen big h site. -/
def bigTopology (X : ChosenBigHSite.{u, v}) (S : X.carrier) :
    GrothendieckTopology (Over S) :=
  X.toGrothendieck.over S

/-- The big h topology over `S` is the slice of the chosen ambient topology. -/
theorem bigTopology_def (X : ChosenBigHSite.{u, v}) (S : X.carrier) :
    bigTopology X S = X.toGrothendieck.over S := sorry

end AlgebraicGeometry.ChosenBigHSite
