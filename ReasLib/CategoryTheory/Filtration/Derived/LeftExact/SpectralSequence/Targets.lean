/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Targets.Abutment
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Targets.PageOne

/-!
# Targets of finite filtered right-derived spectral sequences

Compatibility facade for complex views, pointwise right-derived values, the first page, and the
abutment.  Downstream files needing only one layer should import its semantic leaf directly.
-/

@[expose] public section
