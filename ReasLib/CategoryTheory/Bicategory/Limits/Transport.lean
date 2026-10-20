/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Pseudofunctor.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Pseudofunctor.Modification
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Pseudofunctor.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Functoriality.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Family.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.TransformationFunctor
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Functoriality.Computations

/-!
# Transport of bicategorical pseudocones

This module applies the neutral postcomposition API to conical pseudocones and its readable
pseudo-pullback specialization. Mapping a conical pseudocone is packaged on objects,
`1`-morphisms, and `2`-morphisms as `Pseudofunctor.mapPseudoCone.pseudofunctor`, with explicit unit,
composition, and downstream computation APIs. The conventional four-field pseudo-pullback
presentation has the corresponding `Pseudofunctor.mapPseudoPullbackCone.pseudofunctor`; its
morphism comparisons are obtained from the generic construction by conjugating with the three
canonical presentation comparisons. A strong transformation `E ⟶ F` of diagrams separately
induces `Bicategory.PseudoCone.postcompose : PseudoCone E ⥤ᵖ PseudoCone F`, the bicategorical
counterpart of `Limits.Cone.postcompose`. For a walking-cospan transformation `ψ`, the readable
specialization `Bicategory.PseudoPullbackCone.changeCospan.pseudofunctor ψ` exposes the same
construction without forcing downstream users through the generic pseudocone presentation.
Postcomposition is also functorial in modifications between parallel diagram transformations:
`Bicategory.PseudoCone.postcomposeModificationPseudofunctor` is the complete neutral
opposite-hom action, while `Bicategory.PseudoCone.postcomposeTransformationFunctor` is the
fixed-pseudocone functorial slice,
`Bicategory.PseudoCone.mapDiagram.functor` applies the universal property,
`Bicategory.PseudoPullbackCone.changeCospan.transformation.functor` is its readable facade, and
`Bicategory.PseudoPullbackCone.mapCospan.functor` lifts that action to universal apex maps, with
its readable identity and composition coherence and projection formulas available from this
aggregate. The generic universal-map identity and composition comparisons likewise expose their
vertexwise computation formulas here.
An explicit `Bicategory.BilimitConeFamily` packages one selected bilimit cone for
each diagram; its `apexPseudofunctor` supplies the complete object, `1`-cell, and `2`-cell
action, while `apexEquivalence` and `apexEquivalence.objectProperty_iff` provide the usual downstream
transport along equivalences of diagrams.
Generic transformation and modification postcomposition, as well as the comparison between
mapped and constant diagrams, are owned by `CategoryTheory.Pseudofunctor` and consumed here.

The implementations are organized in focused `Transport.PseudoCone`, `Transport.PseudoPullbackCone`,
and `PseudoPullback.ChangeCospan` leaves. This root remains their compatibility import for
existing downstream users.
-/
