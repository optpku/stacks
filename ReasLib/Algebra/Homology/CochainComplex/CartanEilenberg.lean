/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.AssociatedDerivedPages
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.AlternativeFiltrations
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Augmentation
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.ColumnFunctoriality
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Existence
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.FilteredDerivedTotal
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Rows.Naturality
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.SpectralSequence
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Total.Properties

@[expose] public section

/-!
# Cartan--Eilenberg Resolutions

This aggregate reexports the resolution data, column and row computations, natural initial-page
comparisons, total-complex and right-derived comparisons, the two associated spectral sequences,
and their alternative-filtration constructions. Downstream files that need only one layer should
import its leaf directly.
-/
