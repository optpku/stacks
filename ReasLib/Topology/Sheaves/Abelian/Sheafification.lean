/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.Abelian
public import ReasLib.CategoryTheory.Sites.TypeSheafification

/-!
# Sheafification of abelian-group-valued presheaves on topological spaces

The opens site of a topological space admits the canonical sheafification of
`AddCommGrpCat`-valued presheaves.  Registering this globally avoids rebuilding the same local
instance at every use of abelian sheaves on a space.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Limits

universe w u

namespace TopCat

/-- Abelian-group-valued presheaves on the opens site of a topological space admit
sheafification. -/
noncomputable instance addCommGrpHasSheafify (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w} := by
  -- Local instance justification (proof-local temporary data): The plus-plus adjunction requires the forgetful functor to preserve the cover-indexed colimit for every open U.
  letI : ∀ (U : Opens X), PreservesColimitsOfShape
      ((Opens.grothendieckTopology X).Cover U)ᵒᵖ
      (forget AddCommGrpCat.{max u w}) := fun U => by
    -- Local instance justification (proof-local temporary data): Essential smallness of the opposite cover category supplies the coefficient-universe FinallySmall witness needed for filtered-colimit preservation.
    letI : FinallySmall.{max u w}
        ((Opens.grothendieckTopology X).Cover U)ᵒᵖ :=
      finallySmall_of_essentiallySmall _
    exact FinallySmall.preservesColimitsOfShape_of_isFiltered
      (((Opens.grothendieckTopology X).Cover U)ᵒᵖ)
      (forget AddCommGrpCat.{max u w})
  exact HasSheafify.mk' (J := Opens.grothendieckTopology X)
    (A := AddCommGrpCat.{max u w})
    (plusPlusAdjunction (Opens.grothendieckTopology X) (AddCommGrpCat.{max u w}))

/-- On an opens site, the weak equivalences inverted by abelian sheafification are exactly the
locally bijective morphisms. -/
noncomputable instance addCommGrpWEqualsLocallyBijective (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u w} := by
  let J := Opens.grothendieckTopology X
  let K := (equivSmallModel.{max u w} (Opens X)).inverse.inducedTopology J
  letI : ∀ V : SmallModel.{max u w} (Opens X), PreservesColimitsOfShape
      (K.Cover V)ᵒᵖ (forget AddCommGrpCat.{max u w}) := fun V => by
    letI : FinallySmall.{max u w} (K.Cover V)ᵒᵖ :=
      finallySmall_of_essentiallySmall _
    exact FinallySmall.preservesColimitsOfShape_of_isFiltered
      (K.Cover V)ᵒᵖ (forget AddCommGrpCat.{max u w})
  letI : K.WEqualsLocallyBijective AddCommGrpCat.{max u w} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

/-- Equal-universe specialization of the canonical construction.  Its direct universe pattern
lets typeclass inference determine a space universe from the coefficient universe. -/
noncomputable instance (priority := 1100) addCommGrpHasSheafifySelf (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  addCommGrpHasSheafify.{0, u} X

/-- Equal-universe local-bijectivity law, derived from the same canonical owner. -/
noncomputable instance (priority := 1100) addCommGrpWEqualsLocallyBijectiveSelf (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  addCommGrpWEqualsLocallyBijective.{0, u} X

end TopCat
