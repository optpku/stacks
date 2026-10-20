/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Components
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Constructors
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Inverse
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseAdjunction.Action.StrongTrans

/-!
# Pointwise equivalences of strong transformations

Compatibility aggregate for component data, componentwise constructors,
mate-defined inverses, and assembled equivalences. To act on adjunctions, use
`h.toPointwiseAdjunction.mapAdj`; no duplicate pointwise-equivalence facade is
maintained. New developments can import the narrow leaf matching the API they use.
-/
