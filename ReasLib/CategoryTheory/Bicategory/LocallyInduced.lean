/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.HomProperty
public import ReasLib.CategoryTheory.Bicategory.HomProperty.Equivalence
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Computations
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Iso
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Equivalence
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Factorization
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Lift
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.LocalProperties
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Strict
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.StrongTrans

/-!
# Locally induced bicategories

This is the compatibility entry point for the locally induced bicategory API. New developments
should import the smallest relevant leaf: `Bicategory.HomProperty` for generic hom properties,
`Bicategory.HomProperty.Equivalence` for admissible ambient equivalences,
`LocallyInduced.Construction` for the bicategory construction, `LocallyInduced.Equivalence` for
the canonical equivalence between locally induced equivalences and admissible ambient ones,
`LocallyInduced.Lift` for inclusions and strict-pseudofunctor lifts,
`LocallyInduced.Computations` for projection formulas, `LocallyInduced.Factorization` for
canonical factorization and local-full-faithfulness facts,
`LocallyInduced.LocalProperties` for hom-wise inherited properties, or `LocallyInduced.Strict` for
inherited strictness. The Pseudofunctor leaf provides the corresponding lift for arbitrary
pseudofunctors while retaining their identity and composition comparisons;
`LocallyInduced.Iso` owns ambient projections for locally induced `2`-isomorphisms, `isoMk`,
unitors, and associators;
`LocallyInduced.StrongTrans` is a stable aggregate for the focused
`StrongTrans/{Construction,Computations}` leaves.  The construction leaf provides arbitrary-
pseudofunctor and exact-endpoint strict lifts, together with the canonical transformations
between strict lifts and ambient factorization; the computations leaf provides their ambient
component and naturality readouts.
-/
