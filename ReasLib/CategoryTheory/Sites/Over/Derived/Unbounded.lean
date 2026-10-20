/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Over.Abelian
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Unbounded derived functors on slice sites

For a change of slice base, inverse image on abelian sheaves is exact and therefore acts directly
on unbounded derived categories.  Its right adjoint is represented by the canonical K-injective
total right-derived direct image.  Squares and base-change maps are layered in the separate
`Derived.Square` and `Derived.BaseChange` leaves.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.Derived.Over

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
variable [HasSheafify (J.over X) AddCommGrpCat.{max u v}]
variable [HasSheafify (J.over Y) AddCommGrpCat.{max u v}]

/-- The exact-functor owner for inverse image between abelian sheaves on slice sites. -/
@[stacks 00XY "exact slice inverse image"]
noncomputable abbrev pullbackExact (f : X ⟶ Y) :
    Sheaf (J.over Y) AddCommGrpCat.{max u v} ⥤ₑ
      Sheaf (J.over X) AddCommGrpCat.{max u v} :=
  J.overMapPullbackExact f

/-- The exact inverse-image functor on unbounded derived categories of slice-site sheaves. -/
@[stacks 015F "unbounded derived slice inverse image"]
noncomputable abbrev pullback (f : X ⟶ Y) :
    DerivedCategory (Sheaf (J.over Y) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max u v}) :=
  Adjunction.Derived.KInjective.left (pullbackExact J f)

/-- The localization factor of unbounded derived slice inverse image. -/
@[stacks 015F "unbounded derived slice inverse-image factor"]
noncomputable abbrev pullbackFactor :
    (DerivedCategory.Q :
        CochainComplex (Sheaf (J.over Y) AddCommGrpCat.{max u v}) ℤ ⥤ _) ⋙
        pullback J f ⟶
      (J.overMapPullback AddCommGrpCat.{max u v} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex (Sheaf (J.over X) AddCommGrpCat.{max u v}) ℤ ⥤ _) :=
  Adjunction.Derived.KInjective.leftFactor (pullbackExact J f)

section Pushforward

variable [∀ P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
  (Over.map f).op.HasPointwiseRightKanExtension P]

/-- The K-injective total right-derived direct image between slice sites. -/
@[stacks 05TH "unbounded derived slice direct image"]
noncomputable abbrev pushforward :
    DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf (J.over Y) AddCommGrpCat.{max u v}) :=
  Adjunction.Derived.KInjective.right
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (J.over X) (J.over Y))

/-- The cochain-level unit of unbounded derived slice direct image. -/
@[stacks 05TH "unbounded derived slice direct-image unit"]
noncomputable abbrev pushforwardUnit :
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
        (J.over X) (J.over Y)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Q :
            CochainComplex (Sheaf (J.over Y) AddCommGrpCat.{max u v}) ℤ ⥤ _) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf (J.over X) AddCommGrpCat.{max u v}) ℤ ⥤ _) ⋙
        pushforward J f :=
  Adjunction.Derived.KInjective.rightUnit
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (J.over X) (J.over Y))

/-- The unbounded derived inverse-image/direct-image adjunction on slice sites. -/
@[stacks 05TH "unbounded derived slice adjunction"]
noncomputable def adjunction : pullback J f ⊣ pushforward J f :=
  Adjunction.Derived.KInjective.adjunction (pullbackExact J f)
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (J.over X) (J.over Y))
    (J.overMapCocontinuousAdjunction AddCommGrpCat.{max u v} f)

end Pushforward

end CategoryTheory.GrothendieckTopology.Derived.Over

end
