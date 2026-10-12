/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Ext.TStructure
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.27.3

The vanishing statement is owned at the level of an arbitrary t-structure.
The boundary comparison and its single-degree specializations are owned by
the neutral derived-category Ext API.
-/

/- Lemma 13.27.3 (Stacks 06XS) (1): shifted morphisms vanish below the gap
between an upper and a lower derived t-structure bound. -/
@[stacks 06XS] #check
  @DerivedCategory.ShiftedHom.subsingleton_of_lt_sub

/- Lemma 13.27.3 (Stacks 06XS) (2): at the boundary degree, the canonical
homology comparison is bijective. -/
@[stacks 06XS] #check
  @DerivedCategory.ShiftedHom.Boundary.toHomology_bijective
@[stacks 06XS] #check
  @DerivedCategory.ShiftedHom.Boundary.toHomologyEquiv
@[stacks 06XS] #check
  @DerivedCategory.ShiftedHom.Boundary.toHomologyAddHom
@[stacks 06XS] #check
  @DerivedCategory.ShiftedHom.Boundary.toHomologyAddEquiv
@[stacks 06XS] #check
  @DerivedCategory.ShiftedHom.Boundary.toHomologyAddHom_apply
@[stacks 06XS] #check
  @DerivedCategory.ShiftedHom.Boundary.toHomologyAddEquiv_apply
@[stacks 06XS] #check
  @DerivedCategory.ShiftedHom.Boundary.toHomologyEquiv_naturality_left
@[stacks 06XS] #check
  @DerivedCategory.ShiftedHom.Boundary.toHomologyEquiv_naturality_right

/- Lemma 13.27.3 (Stacks 06XS) (3): negative shifted morphisms between
single-degree objects vanish. -/
@[stacks 06XS] #check
  @DerivedCategory.Single.ShiftedHom.subsingleton_of_neg

/- Lemma 13.27.3 (Stacks 06XS) (4): degree-zero shifted morphisms between
single-degree objects are ordinary morphisms in the abelian category. -/
@[stacks 06XS] #check
  @DerivedCategory.Single.ShiftedHom.zeroEquiv
