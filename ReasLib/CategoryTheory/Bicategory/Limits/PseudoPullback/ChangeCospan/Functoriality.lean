/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Functoriality.Identity
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Functoriality.Composition

/-!
# Functoriality of readable change of cospan

This compatibility module collects the identity and composition comparisons for the action on
readable pseudopullback-cone morphisms.  The underlying action itself is owned by
`ChangeCospan.Hom`.
-/

@[expose] public section
