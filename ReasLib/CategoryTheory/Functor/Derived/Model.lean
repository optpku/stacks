module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit models of derived functors

The typeclass predicates `IsLeftDerivedFunctor` and `IsRightDerivedFunctor` describe laws of a
chosen model, while `HasLeftDerivedFunctor` and `HasRightDerivedFunctor` only assert existence.
This leaf packages the concrete functor and comparison morphism together with the relevant law,
so downstream constructions can consume an explicit model without choosing data from a Prop.
-/

@[expose] public section

universe vC vD vH uC uD uH

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} {H : Type uH}
  [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]

namespace LeftDerived

/-- An explicit left-derived model for `F` along the localization `L` of `W`.

The functor and counit are concrete fields; `isLeftDerived` records the right-Kan-extension law.
-/
@[stacks 05SA "explicit left-derived functor model"]
structure Model (F : C ⥤ H) (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] where
  /-- The chosen left-derived functor. -/
  functor : D ⥤ H
  /-- The comparison counit from the localized functor to the source functor. -/
  counit : L ⋙ functor ⟶ F
  /-- The counit exhibits `functor` as a left-derived functor. -/
  isLeftDerived : functor.IsLeftDerivedFunctor counit W

/-- The left-derived-functor law carried by an explicit model, exposed as an explicit proof term
for APIs whose model argument is already explicit. -/
@[stacks 05SA "left-derived model law"]
abbrev Model.isLeftDerivedFunctor {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M : Model F L W) :
    M.functor.IsLeftDerivedFunctor M.counit W :=
  M.isLeftDerived

/-- Construct an explicit left-derived model from concrete functor and counit data and its
universal-property law. -/
@[stacks 05SA "left-derived model constructor"]
def Model.of {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (functor : D ⥤ H) (counit : L ⋙ functor ⟶ F)
    (h : functor.IsLeftDerivedFunctor counit W) : Model F L W :=
  { functor := functor, counit := counit, isLeftDerived := h }

/-- Transport the counit of an explicit left-derived model to an isomorphic functor. -/
@[stacks 05SA "transported left-derived model counit"]
noncomputable def Model.counitOfIso {F : C ⥤ H} {L : C ⥤ D}
    {W : MorphismProperty C} [L.IsLocalization W] (M : Model F L W)
    (G : D ⥤ H) (e : M.functor ≅ G) : L ⋙ G ⟶ F :=
  Functor.whiskerLeft L e.inv ≫ M.counit

/-- The canonical isomorphism between two explicit left-derived models of the same functor. -/
@[stacks 05SA "left-derived model comparison"]
noncomputable abbrev Model.iso {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M N : Model F L W) : M.functor ≅ N.functor :=
  @Functor.leftDerivedUnique _ _ _ _ _ _ N.functor M.functor
    (F := F) (L := L) M.counit N.counit W (inferInstance)
    M.isLeftDerivedFunctor N.isLeftDerivedFunctor

/-- The canonical comparison between left-derived models intertwines their counits. -/
@[reassoc, stacks 05SA "left-derived model counit compatibility"]
theorem Model.iso_hom_counit {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M N : Model F L W) :
    Functor.whiskerLeft L (M.iso N).hom ≫ N.counit = M.counit := by
  exact
    (@Functor.leftDerivedNatTrans_fac _ _ _ _ _ _ M.functor N.functor
      (F := F) (F' := F) (L := L) M.counit N.counit W (inferInstance)
      N.isLeftDerived (𝟙 F)).trans (Category.comp_id M.counit)

/-- The objectwise canonical isomorphism between two explicit left-derived models. -/
@[stacks 05SA "left-derived object model comparison"]
noncomputable abbrev Model.isoApp {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M N : Model F L W) (X : D) :
    M.functor.obj X ≅ N.functor.obj X :=
  (M.iso N).app X

set_option backward.isDefEq.respectTransparency false in
/-- Objectwise counit compatibility for the canonical comparison between left-derived models. -/
@[reassoc, stacks 05SA "left-derived object model counit compatibility"]
theorem Model.isoApp_hom_counit {F : C ⥤ H} {L : C ⥤ D}
    {W : MorphismProperty C} [L.IsLocalization W] (M N : Model F L W) (X : C) :
    (M.isoApp N (L.obj X)).hom ≫ N.counit.app X = M.counit.app X := by
  change (Functor.whiskerLeft L (M.iso N).hom ≫ N.counit).app X =
    M.counit.app X
  exact NatTrans.congr_app (M.iso_hom_counit N) X

/-- The canonical comparison of a left-derived model with itself is the identity. -/
@[stacks 05SA "left-derived model comparison reflexivity"]
theorem Model.iso_refl {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M : Model F L W) :
    M.iso M = Iso.refl M.functor := by
  apply Iso.ext
  apply @Functor.leftDerived_ext _ _ _ _ _ _ M.functor
    (F := F) (L := L) M.counit W (inferInstance) M.isLeftDerived
  rw [M.iso_hom_counit M]
  simp

/-- Reversing the canonical comparison of left-derived models exchanges its endpoints. -/
@[stacks 05SA "left-derived model comparison symmetry"]
theorem Model.iso_symm {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M N : Model F L W) :
    (M.iso N).symm = N.iso M := by
  apply Iso.ext
  apply @Functor.leftDerived_ext _ _ _ _ _ _ M.functor
    (F := F) (L := L) M.counit W (inferInstance) M.isLeftDerived
  rw [N.iso_hom_counit M]
  rw [← M.iso_hom_counit N]
  simp

/-- Canonical comparisons of left-derived models compose transitively. -/
@[stacks 05SA "left-derived model comparison transitivity"]
theorem Model.iso_trans {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M N P : Model F L W) :
    (M.iso N).trans (N.iso P) = M.iso P := by
  apply Iso.ext
  apply @Functor.leftDerived_ext _ _ _ _ _ _ P.functor
    (F := F) (L := L) P.counit W (inferInstance) P.isLeftDerived
  rw [M.iso_hom_counit P]
  simp only [Iso.trans_hom, Functor.whiskerLeft_comp, Category.assoc]
  rw [N.iso_hom_counit P, M.iso_hom_counit N]

end LeftDerived

namespace RightDerived

/-- An explicit right-derived model for `F` along the localization `L` of `W`.

The functor and unit are concrete fields; `isRightDerived` records the left-Kan-extension law.
-/
@[stacks 05SA "explicit right-derived functor model"]
structure Model (F : C ⥤ H) (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] where
  /-- The chosen right-derived functor. -/
  functor : D ⥤ H
  /-- The comparison unit from the source functor to the localized functor. -/
  unit : F ⟶ L ⋙ functor
  /-- The unit exhibits `functor` as a right-derived functor. -/
  isRightDerived : functor.IsRightDerivedFunctor unit W

/-- The right-derived-functor law carried by an explicit model, exposed as an explicit proof term
for APIs whose model argument is already explicit. -/
@[stacks 05SA "right-derived model law"]
abbrev Model.isRightDerivedFunctor {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M : Model F L W) :
    M.functor.IsRightDerivedFunctor M.unit W :=
  M.isRightDerived

/-- Construct an explicit right-derived model from concrete functor and unit data and its
universal-property law. -/
@[stacks 05SA "right-derived model constructor"]
def Model.of {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (functor : D ⥤ H) (unit : F ⟶ L ⋙ functor)
    (h : functor.IsRightDerivedFunctor unit W) : Model F L W :=
  { functor := functor, unit := unit, isRightDerived := h }

/-- Transport the unit of an explicit right-derived model to an isomorphic functor. -/
@[stacks 05SA "transported right-derived model unit"]
noncomputable def Model.unitOfIso {F : C ⥤ H} {L : C ⥤ D}
    {W : MorphismProperty C} [L.IsLocalization W] (M : Model F L W)
    (G : D ⥤ H) (e : M.functor ≅ G) : F ⟶ L ⋙ G :=
  M.unit ≫ Functor.whiskerLeft L e.hom

/-- The canonical isomorphism between two explicit right-derived models of the same functor. -/
@[stacks 05SA "right-derived model comparison"]
noncomputable abbrev Model.iso {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M N : Model F L W) : M.functor ≅ N.functor :=
  @Functor.rightDerivedUnique _ _ _ _ _ _ M.functor N.functor
    (F := F) (L := L) M.unit N.unit W (inferInstance)
    M.isRightDerivedFunctor N.isRightDerivedFunctor

/-- The canonical comparison between right-derived models intertwines their units. -/
@[reassoc, stacks 05SA "right-derived model unit compatibility"]
theorem Model.unit_iso_hom {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M N : Model F L W) :
    M.unit ≫ Functor.whiskerLeft L (M.iso N).hom = N.unit := by
  exact
    (@Functor.rightDerivedNatTrans_fac _ _ _ _ _ _ M.functor N.functor
      (F := F) (F' := F) (L := L) M.unit N.unit W (inferInstance)
      M.isRightDerived (𝟙 F)).trans (Category.id_comp N.unit)

/-- The objectwise canonical isomorphism between two explicit right-derived models. -/
@[stacks 05SA "right-derived object model comparison"]
noncomputable abbrev Model.isoApp {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M N : Model F L W) (X : D) :
    M.functor.obj X ≅ N.functor.obj X :=
  (M.iso N).app X

set_option backward.isDefEq.respectTransparency false in
/-- Objectwise unit compatibility for the canonical comparison between right-derived models. -/
@[reassoc, stacks 05SA "right-derived object model unit compatibility"]
theorem Model.unit_isoApp_hom {F : C ⥤ H} {L : C ⥤ D}
    {W : MorphismProperty C} [L.IsLocalization W] (M N : Model F L W) (X : C) :
    M.unit.app X ≫ (M.isoApp N (L.obj X)).hom = N.unit.app X := by
  change (M.unit ≫ Functor.whiskerLeft L (M.iso N).hom).app X =
    N.unit.app X
  exact NatTrans.congr_app (M.unit_iso_hom N) X

/-- The canonical comparison of a right-derived model with itself is the identity. -/
@[stacks 05SA "right-derived model comparison reflexivity"]
theorem Model.iso_refl {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M : Model F L W) :
    M.iso M = Iso.refl M.functor := by
  apply Iso.ext
  apply @Functor.rightDerived_ext _ _ _ _ _ _ M.functor
    (F := F) (L := L) M.unit W (inferInstance) M.isRightDerived
  rw [M.unit_iso_hom M]
  simp

/-- Reversing the canonical comparison of right-derived models exchanges its endpoints. -/
@[stacks 05SA "right-derived model comparison symmetry"]
theorem Model.iso_symm {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M N : Model F L W) :
    (M.iso N).symm = N.iso M := by
  apply Iso.ext
  apply @Functor.rightDerived_ext _ _ _ _ _ _ N.functor
    (F := F) (L := L) N.unit W (inferInstance) N.isRightDerived
  rw [N.unit_iso_hom M]
  rw [← M.unit_iso_hom N]
  simp

/-- Canonical comparisons of right-derived models compose transitively. -/
@[stacks 05SA "right-derived model comparison transitivity"]
theorem Model.iso_trans {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (M N P : Model F L W) :
    (M.iso N).trans (N.iso P) = M.iso P := by
  apply Iso.ext
  apply @Functor.rightDerived_ext _ _ _ _ _ _ M.functor
    (F := F) (L := L) M.unit W (inferInstance) M.isRightDerived
  rw [M.unit_iso_hom P]
  simp only [Iso.trans_hom, Functor.whiskerLeft_comp]
  rw [← Category.assoc, M.unit_iso_hom N, N.unit_iso_hom P]

end RightDerived

end CategoryTheory.Functor
