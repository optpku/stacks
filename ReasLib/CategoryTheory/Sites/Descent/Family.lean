/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Family.DescentDatum
public import ReasLib.CategoryTheory.Sites.Descent.Family.Overlap.Choice
public import ReasLib.CategoryTheory.Sites.Descent.Family.Presentation.Change
public import ReasLib.CategoryTheory.Sites.Descent.Family.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.Family.Refinement
public import ReasLib.CategoryTheory.Sites.Descent.Family.Coherence
public import ReasLib.CategoryTheory.Sites.Descent.Family.Canonical

/-!
# Descent data for fixed-target families

This is the stable aggregate for canonical family descent data, chosen-overlap presentations,
pullback functoriality, and overlap-specific coherence. Consumers should import the narrowest leaf
that owns the API they use.
-/
