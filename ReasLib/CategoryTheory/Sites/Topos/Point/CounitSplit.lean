/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.TypeCounit
public import ReasLib.CategoryTheory.Sites.Topos.Point.TypeImage

/-!
# Splitting the counit of a topos point

This specializes `Adjunction.counitSection` to the `Type`-valued inverse and
direct images of a point of a topos.  The site-specific input is only that an
inverse image functor preserves the terminal object.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

noncomputable section

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- The canonical natural section of the counit of the `Type`-valued
adjunction of a topos point. -/
noncomputable def typeCounitSection
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    𝟭 (Type w) ⟶ p.typePushforward ⋙ p.typeInverseImage :=
  p.typeAdjunction.counitSection

/-- Lemma 7.32.9 (05UX): the canonical counit map
`p^{-1}(p_* E) ⟶ E` admits the canonical section
`(p.typeCounitSection.app E)`. -/
@[stacks 05UX]
theorem typeCounitSection_leftInverse
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) (E : Type w) :
    Function.LeftInverse ((p.typeAdjunction.counit).app E) (p.typeCounitSection.app E) := sorry

/-- The counit map `p^{-1}(p_* E) ⟶ E` of a topos point is split epic. -/
theorem typeCounit_isSplitEpi
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) (E : Type w) :
    IsSplitEpi ((p.typeAdjunction.counit).app E) := sorry

end CategoryTheory.MorphismOfTopoiIn
