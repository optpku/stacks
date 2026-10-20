/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Closure
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.ProductSlice
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pair
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Cartesian
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.GerbeMorphism
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fibered
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.ChosenCleavage
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Bilimit
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Comparison
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.FstFiber
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.SndFiber
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Graph
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex

/-!
# Explicit pseudo-pullbacks of categories over a base

This is the broad aggregate import for the explicit pseudo-pullback construction in Cat/C.
The implementation is organized by mathematical layer:

* Basic: explicit objects, morphisms, and their component API;
* Iso, Projections, Cartesian, and GerbeMorphism: intrinsic pseudo-pullback structure and local
  properties of its cartesian projections;
* Fibered and ChosenCleavage: the application-facing bundle and its instance-aligned choice boundary;
* Functoriality: cospan actions, their coherence, and 2-cell action;
* Pseudofunctor: the bundled cospan pseudofunctor;
* Symmetry: swapping, its involutivity/equivalence, and the layered `Symmetry` readout API;
* Bilimit: the bicategorical universal-property bridge;
* Comparison, Fiber, FstFiber, and SndFiber: categorical and fibrewise comparison equivalences;
* Graph and Reindex: graph equivalences and explicit or canonically chosen fibre reindexing.

New developments should import the smallest leaf that provides their required API. This aggregate
remains the broad entry point for developments that need the complete construction.
-/
