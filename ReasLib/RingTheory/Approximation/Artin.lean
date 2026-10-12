/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Approximation.Artin.Etale.AtClosedPoint.Existence
public import ReasLib.RingTheory.Approximation.Artin.Etale.AtPrime.Existence
public import ReasLib.RingTheory.Approximation.Artin.Henselian
public import ReasLib.RingTheory.Approximation.Artin.Local

@[expose] public section

/-!
# Artin approximation

This is the stable aggregate import for Artin approximation.  Clients that
only need the henselian-pair, local, closed-point, or primewise theorem can
import the corresponding `Artin` leaf directly.
-/
