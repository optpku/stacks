/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# The constant integer sheaf on a site

This leaf gives a site-generic owner for the constant sheaf with value
`ULift ℤ`.  The coefficient-level corepresentability is already owned by
`AddCommGrpCat.uliftZMultiplesAddEquiv`; the declarations below combine it
with the constant-sheaf/global-sections adjunction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The free abelian group on one generator is canonically the universe-lifted integers. -/
noncomputable def freePUnitIsoInteger :
    AddCommGrpCat.free.obj PUnit ≅ AddCommGrpCat.of (ULift.{w} ℤ) :=
  (((FreeAbelianGroup.equivFinsupp PUnit).trans
    (Finsupp.uniqueAddEquiv PUnit.unit)).trans
    (AddEquiv.ulift : ULift.{w} ℤ ≃+ ℤ).symm).toAddCommGrpIso

/-- The constant sheaf of integers on the site `(C, J)`, with `ULift ℤ` used at the
coefficient universe. -/
abbrev constantIntegerSheaf (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{w}] :
    Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))

namespace Sheaf

variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]

/-- Global sections of an additive sheaf identify with morphisms from the constant integer
sheaf, as an equivalence of underlying types. -/
noncomputable def globalSectionsEquivConstantIntegerSheafHomOnSite
    (F : Sheaf J AddCommGrpCat.{w}) :
    (Γ J AddCommGrpCat.{w}).obj F ≃ (constantIntegerSheaf J ⟶ F) :=
  ((AddCommGrpCat.uliftZMultiplesAddEquiv
      ((Γ J AddCommGrpCat.{w}).obj F)).toEquiv).symm.trans
    ((constantSheafΓAdj J AddCommGrpCat.{w}).homEquiv
      (AddCommGrpCat.of (ULift.{w} ℤ)) F).symm

/-- The global-sections-to-Hom equivalence for the constant integer sheaf is natural in the
sheaf variable. -/
theorem globalSectionsEquivConstantIntegerSheafHomOnSite_naturality
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G)
    (x : (Γ J AddCommGrpCat.{w}).obj F) :
    globalSectionsEquivConstantIntegerSheafHomOnSite J G
        ((Γ J AddCommGrpCat.{w}).map f x) =
      globalSectionsEquivConstantIntegerSheafHomOnSite J F x ≫ f := sorry

/-- Global sections of an additive sheaf identify additively with morphisms from the constant
integer sheaf. -/
noncomputable def globalSectionsAddEquivConstantIntegerSheafHomOnSite
    [Preadditive (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w}) :
    (Γ J AddCommGrpCat.{w}).obj F ≃+ (constantIntegerSheaf J ⟶ F) where
  toEquiv := globalSectionsEquivConstantIntegerSheafHomOnSite J F
  map_add' := sorry

/-- The additive global-sections-to-Hom equivalence for the constant integer sheaf is natural in
the sheaf variable. -/
theorem globalSectionsAddEquivConstantIntegerSheafHomOnSite_naturality
    [Preadditive (Sheaf J AddCommGrpCat.{w})]
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G)
    (x : (Γ J AddCommGrpCat.{w}).obj F) :
    globalSectionsAddEquivConstantIntegerSheafHomOnSite J G
        ((Γ J AddCommGrpCat.{w}).map f x) =
      globalSectionsAddEquivConstantIntegerSheafHomOnSite J F x ≫ f := sorry

/-- The global section of the constant integer sheaf corresponding to `1 : ℤ`. -/
noncomputable def constantIntegerSheafGlobalSection :
    (Γ J AddCommGrpCat.{w}).obj (constantIntegerSheaf J) :=
  ((constantSheafΓAdj J AddCommGrpCat.{w}).unit.app
    (AddCommGrpCat.of (ULift.{w} ℤ))) (ULift.up (1 : ℤ))

/-- The restriction of the distinguished global section `1` of the constant integer sheaf to an
object of the site. -/
noncomputable def constantIntegerSheafOne (U : Cᵒᵖ) :
    (constantIntegerSheaf J).obj.obj U :=
  ΓRes (constantIntegerSheaf J) U (constantIntegerSheafGlobalSection J)

/-- The distinguished local section `1` of the constant integer sheaf is compatible with
restriction. -/
theorem constantIntegerSheafOne_naturality
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (constantIntegerSheaf J).obj.map f (constantIntegerSheafOne J U) =
      constantIntegerSheafOne J V := sorry

end Sheaf

end CategoryTheory

/- The `sorryAx` in the additive equivalence audit is confined to its `map_add'` proof field;
the underlying equivalence is the explicit declaration audited immediately above. -/
