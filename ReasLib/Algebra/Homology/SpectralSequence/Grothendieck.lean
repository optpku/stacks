/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Existence
public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Degeneration
public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Functorial
public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.IsIso
public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.Total
public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.Total.IsIso
public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.Total.Comparison

/-!
# Grothendieck Spectral-Sequence API

This umbrella exposes the neutral realization, total category, forgetful functors, page-two and
abutment comparisons, morphism naturality, and canonical existence interfaces for Grothendieck
spectral sequences.
-/

@[expose] public section

open CategoryTheory
