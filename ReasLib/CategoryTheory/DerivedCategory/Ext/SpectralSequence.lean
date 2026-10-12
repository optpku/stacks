/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Filtered
public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Functor
public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Target
public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Source
public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Target.Realization
public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Source.Realization

/-!
# Extension Spectral Sequences

This aggregate exposes the elementary objects, general filtered models, their functoriality and
naturality API, and the target- and source-side canonical specializations. Downstream files can
import the corresponding leaf when only one layer is needed.
-/

@[expose] public section

open CategoryTheory
