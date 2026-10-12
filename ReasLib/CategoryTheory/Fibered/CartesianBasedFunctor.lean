/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Cospan.PrecompLift
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.PrecompLift
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex.PullHom

/-!
# Cartesian based functors

This convenience module exports the cleavage-independent owner, postcomposition and
precomposition (including explicit quasi-inverse lifts and their cospan assembly), its optional
cleavage-reindexing comparison API, and the descent-facing `pullHom` coherence. The
comparison readout is `CartesianBasedFunctor.Reindex.mapIso`, with
`Hom`, `Inv`, `Naturality`, `Conjugation`, `Comp`, `Id`, and `SpecifiedComp`, together with
`CartesianBasedFunctor.Reindex.natIso` and `NatIso.Component`.
-/
