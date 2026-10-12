/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseAdjunction
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.MapAdjunctions

/-!
# Application-level naturality for strong transformations

Compatibility aggregate for precomposition, postcomposition, constant-diagram preservation,
pointwise evaluation, strong-transformation components, pointwise adjunctions and
equivalences, and the action on adjunctions. New developments should import the smallest
corresponding leaf.
-/
