/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Functor
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Shift
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Shift
public import ReasLib.CategoryTheory.MorphismProperty.Shift.InverseImage
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Equivalence.Invariance
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Shift
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localizing the Essential-Constancy Domain of a Derived Functor

Stacks 05SE concerns the full subcategory `E` of objects at which `RF` (resp. `LF`) is defined in
the sense of 05S9, i.e. where the localization-indexed diagram is essentially constant.  This leaf
restricts the denominators to `E`, records that they are morphisms of `E` (part (3)) and are
inverted by the derived functor (part (4)), and provides the induced factorization of the derived
functor through the localization of `E` (part (7)), together with the canonical shift
comparisons.  The triangulated parts live in `DefinedAt.Triangulated`.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Localization MorphismProperty ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

namespace Functor.RightDerived.DefinedAt

/-- The localization class obtained by restricting `S` to the essential-constancy domain
`E` of the right-derived functor: `S_E = Arrows(E) ∩ S`. -/
@[stacks 05SE "restricted denominators on the right essential-constancy domain"]
abbrev system : MorphismProperty (Domain F S) :=
  fullSubcategoryLocalizationSystem (objects F S) S

namespace objects

/-- An element of `S` whose source lies in the right essential-constancy domain has its target
in that domain. -/
@[stacks 05SE "(3), right-derived, source"]
instance inheritedFromSource [IsSaturatedMultiplicativeSystem S] :
    (objects F S).InheritedFromSource S := sorry

/-- An element of `S` whose target lies in the right essential-constancy domain has its source
in that domain. -/
@[stacks 05SE "(3), right-derived, target"]
instance inheritedFromTarget [IsSaturatedMultiplicativeSystem S] :
    (objects F S).InheritedFromTarget S := sorry

end objects

/-- The right-derived functor on its essential-constancy domain inverts the restricted
denominators. -/
@[stacks 05SE "(4), right-derived"]
theorem functor.isInvertedBy [IsSaturatedMultiplicativeSystem S] :
    (system F S).IsInvertedBy (functor F S) := by
  intro X Y f hf
  letI : Limits.HasColimit (CostructuredArrow.map (S.Q.map f.hom) ⋙
      CostructuredArrow.proj S.Q (S.Q.obj Y.obj) ⋙ F) :=
    inferInstanceAs (Limits.HasColimit (CostructuredArrow.proj S.Q (S.Q.obj X.obj) ⋙ F))
  change IsIso (Limits.colimit.pre (CostructuredArrow.proj S.Q (S.Q.obj Y.obj) ⋙ F)
    (CostructuredArrow.map (S.Q.map f.hom)))
  change IsIso (Limits.colimit.pre (CostructuredArrow.proj S.Q (S.Q.obj Y.obj) ⋙ F)
    (CostructuredArrow.mapIso (Localization.Construction.wIso f.hom hf)).functor)
  infer_instance

/-- The factorization of the right-derived functor on its essential-constancy domain through the
localization `S_E⁻¹ E`. Original arrows act by the value map; formal inverses act by colimit descent
along the formal inverse in the ambient localization. -/
@[stacks 05SE "(7), right-derived factorization"]
noncomputable abbrev localizationFactorization [IsSaturatedMultiplicativeSystem S] :
    (system F S).Localization ⥤ D' :=
  Quotient.lift (Localization.Construction.relations (system F S))
    (Quiv.lift
      { obj := fun X ↦ (functor F S).obj X.obj
        map := by
          intro X Y
          rintro (f | ⟨f, hf⟩)
          · exact (functor F S).map f
          · letI : F.HasPointwiseRightDerivedFunctorAt S X.obj.obj :=
              lePointwise F S _ X.obj.property
            letI : F.HasPointwiseRightDerivedFunctorAt S Y.obj.obj :=
              lePointwise F S _ Y.obj.property
            exact Limits.colimit.desc
              (CostructuredArrow.proj S.Q (S.Q.obj X.obj.obj) ⋙ F)
              { pt := (functor F S).obj Y.obj
                ι :=
                  { app := fun g ↦ Limits.colimit.ι
                      (CostructuredArrow.proj S.Q (S.Q.obj Y.obj.obj) ⋙ F)
                      (CostructuredArrow.mk
                        (g.hom ≫ (Localization.Construction.wIso f.hom hf).inv))
                    naturality := by intros; sorry } } })
    (by intros; sorry)

/-- The canonical comparison between the localized right-derived factorization and the
right-derived functor on the essential-constancy domain. -/
@[stacks 05SE "right-derived factorization comparison"]
noncomputable def facIso [IsSaturatedMultiplicativeSystem S] :
    (system F S).Q ⋙ localizationFactorization F S ≅ functor F S :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; sorry)

/-- The explicit factorization carries its canonical comparison with the original functor. -/
noncomputable instance localizationFactorization.lifting [IsSaturatedMultiplicativeSystem S] :
    Localization.Lifting (system F S).Q (system F S) (functor F S)
      (localizationFactorization F S) :=
  ⟨facIso F S⟩

namespace localizationFactorization

/-- The localized right-derived factorization maps a localized morphism of the domain by
conjugating the canonical pointwise value map with the factorization comparison. -/
@[stacks 05SE "right-derived factorization on localized morphisms"]
theorem map_Q [IsSaturatedMultiplicativeSystem S] {X Y : Domain F S} (f : X ⟶ Y) :
    (localizationFactorization F S).map ((system F S).Q.map f) =
      (facIso F S).hom.app X ≫ RightDerived.Value.map F S f.hom ≫
        (facIso F S).inv.app Y := sorry

end localizationFactorization

section Shift

variable [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]

/-- The inclusion of the essential-constancy domain into the pointwise-existence domain commutes
with shifts; its comparison is transported from the two full-subcategory inclusions. -/
@[stacks 05SE "shift comparison of the right domain inclusion"]
noncomputable instance Domain.toPointwise.commShift : (Domain.toPointwise F S).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents
    (fun X ↦ (Definedness.property F S).isoMk
      (((objects F S).ι.commShiftIso n).app X ≪≫
        (((Definedness.property F S).ι.commShiftIso n).app
          ((Domain.toPointwise F S).obj X)).symm))
    (by intros; sorry)
  commShiftIso_zero := by sorry
  commShiftIso_add := by intros; sorry

/-- The right-derived functor on its essential-constancy domain commutes with shifts. -/
@[stacks 05SE "(2), right-derived shift compatibility"]
noncomputable instance functor.commShift : (functor F S).CommShift ℤ :=
  inferInstanceAs ((Domain.toPointwise F S ⋙ Definedness.functor F S).CommShift ℤ)

/-- The localized right-derived factorization commutes with shifts, using its comparison on
the original object underlying each localization object. -/
@[stacks 05SE "(7), right-derived factorization shift compatibility"]
noncomputable instance localizationFactorization.commShift [IsSaturatedMultiplicativeSystem S] :
    (localizationFactorization F S).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents
    (fun X ↦
      let A := (Localization.Construction.objEquiv (system F S)).symm X
      (localizationFactorization F S).mapIso
          (((system F S).Q.commShiftIso n).app A).symm ≪≫
        (facIso F S).app (A⟦n⟧) ≪≫
        ((functor F S).commShiftIso n).app A ≪≫
        (shiftFunctor D' n).mapIso ((facIso F S).app A).symm)
    (by intros; sorry)
  commShiftIso_zero := by sorry
  commShiftIso_add := by intros; sorry

/-- The right-derived factorization comparison is compatible with shifts. -/
@[stacks 05SE "right-derived factorization comparison shift compatibility"]
noncomputable instance facIso.homCommShift [IsSaturatedMultiplicativeSystem S] :
    NatTrans.CommShift (facIso F S).hom ℤ where
  shift_comm := by intros; sorry

end Shift

end Functor.RightDerived.DefinedAt

namespace Functor.LeftDerived.DefinedAt

/-- The localization class obtained by restricting `S` to the essential-constancy domain
`E` of the left-derived functor: `S_E = Arrows(E) ∩ S`. -/
@[stacks 05SE "restricted denominators on the left essential-constancy domain"]
abbrev system : MorphismProperty (Domain F S) :=
  fullSubcategoryLocalizationSystem (objects F S) S

namespace objects

/-- An element of `S` whose source lies in the left essential-constancy domain has its target
in that domain. -/
@[stacks 05SE "(3), left-derived, source"]
instance inheritedFromSource [IsSaturatedMultiplicativeSystem S] :
    (objects F S).InheritedFromSource S := sorry

/-- An element of `S` whose target lies in the left essential-constancy domain has its source
in that domain. -/
@[stacks 05SE "(3), left-derived, target"]
instance inheritedFromTarget [IsSaturatedMultiplicativeSystem S] :
    (objects F S).InheritedFromTarget S := sorry

end objects

/-- The left-derived functor on its essential-constancy domain inverts the restricted
denominators. -/
@[stacks 05SE "(4), left-derived"]
theorem functor.isInvertedBy [IsSaturatedMultiplicativeSystem S] :
    (system F S).IsInvertedBy (functor F S) := by
  intro X Y f hf
  letI : Limits.HasLimit (StructuredArrow.map (S.Q.map f.hom) ⋙
      StructuredArrow.proj (S.Q.obj X.obj) S.Q ⋙ F) :=
    inferInstanceAs (Limits.HasLimit (StructuredArrow.proj (S.Q.obj Y.obj) S.Q ⋙ F))
  change IsIso (Limits.limit.pre (StructuredArrow.proj (S.Q.obj X.obj) S.Q ⋙ F)
    (StructuredArrow.map (S.Q.map f.hom)))
  change IsIso (Limits.limit.pre (StructuredArrow.proj (S.Q.obj X.obj) S.Q ⋙ F)
    (StructuredArrow.mapIso (Localization.Construction.wIso f.hom hf).symm).functor)
  infer_instance

/-- The factorization of the left-derived functor on its essential-constancy domain through the
localization `S_E⁻¹ E`. Original arrows act by the value map; formal inverses act by limit lifting
along the formal inverse in the ambient localization. -/
@[stacks 05SE "(7), left-derived factorization"]
noncomputable abbrev localizationFactorization [IsSaturatedMultiplicativeSystem S] :
    (system F S).Localization ⥤ D' :=
  Quotient.lift (Localization.Construction.relations (system F S))
    (Quiv.lift
      { obj := fun X ↦ (functor F S).obj X.obj
        map := by
          intro X Y
          rintro (f | ⟨f, hf⟩)
          · exact (functor F S).map f
          · letI : F.HasPointwiseLeftDerivedFunctorAt S X.obj.obj :=
              lePointwise F S _ X.obj.property
            letI : F.HasPointwiseLeftDerivedFunctorAt S Y.obj.obj :=
              lePointwise F S _ Y.obj.property
            exact Limits.limit.lift
              (StructuredArrow.proj (S.Q.obj Y.obj.obj) S.Q ⋙ F)
              { pt := (functor F S).obj X.obj
                π :=
                  { app := fun g ↦ Limits.limit.π
                      (StructuredArrow.proj (S.Q.obj X.obj.obj) S.Q ⋙ F)
                      (StructuredArrow.mk
                        ((Localization.Construction.wIso f.hom hf).inv ≫ g.hom))
                    naturality := by intros; sorry } } })
    (by intros; sorry)

/-- The canonical comparison between the localized left-derived factorization and the
left-derived functor on the essential-constancy domain. -/
@[stacks 05SE "left-derived factorization comparison"]
noncomputable def facIso [IsSaturatedMultiplicativeSystem S] :
    (system F S).Q ⋙ localizationFactorization F S ≅ functor F S :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; sorry)

/-- The explicit factorization carries its canonical comparison with the original functor. -/
noncomputable instance localizationFactorization.lifting [IsSaturatedMultiplicativeSystem S] :
    Localization.Lifting (system F S).Q (system F S) (functor F S)
      (localizationFactorization F S) :=
  ⟨facIso F S⟩

namespace localizationFactorization

/-- The localized left-derived factorization maps a localized morphism of the domain by
conjugating the canonical pointwise value map with the factorization comparison. -/
@[stacks 05SE "left-derived factorization on localized morphisms"]
theorem map_Q [IsSaturatedMultiplicativeSystem S] {X Y : Domain F S} (f : X ⟶ Y) :
    (localizationFactorization F S).map ((system F S).Q.map f) =
      (facIso F S).hom.app X ≫ LeftDerived.Value.map F S f.hom ≫
        (facIso F S).inv.app Y := sorry

end localizationFactorization

section Shift

variable [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]

/-- The inclusion of the essential-constancy domain into the pointwise-existence domain commutes
with shifts; its comparison is transported from the two full-subcategory inclusions. -/
@[stacks 05SE "shift comparison of the left domain inclusion"]
noncomputable instance Domain.toPointwise.commShift : (Domain.toPointwise F S).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents
    (fun X ↦ (Definedness.property F S).isoMk
      (((objects F S).ι.commShiftIso n).app X ≪≫
        (((Definedness.property F S).ι.commShiftIso n).app
          ((Domain.toPointwise F S).obj X)).symm))
    (by intros; sorry)
  commShiftIso_zero := by sorry
  commShiftIso_add := by intros; sorry

/-- The left-derived functor on its essential-constancy domain commutes with shifts. -/
@[stacks 05SE "(2), left-derived shift compatibility"]
noncomputable instance functor.commShift : (functor F S).CommShift ℤ :=
  inferInstanceAs ((Domain.toPointwise F S ⋙ Definedness.functor F S).CommShift ℤ)

/-- The localized left-derived factorization commutes with shifts, using its comparison on
the original object underlying each localization object. -/
@[stacks 05SE "(7), left-derived factorization shift compatibility"]
noncomputable instance localizationFactorization.commShift [IsSaturatedMultiplicativeSystem S] :
    (localizationFactorization F S).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents
    (fun X ↦
      let A := (Localization.Construction.objEquiv (system F S)).symm X
      (localizationFactorization F S).mapIso
          (((system F S).Q.commShiftIso n).app A).symm ≪≫
        (facIso F S).app (A⟦n⟧) ≪≫
        ((functor F S).commShiftIso n).app A ≪≫
        (shiftFunctor D' n).mapIso ((facIso F S).app A).symm)
    (by intros; sorry)
  commShiftIso_zero := by sorry
  commShiftIso_add := by intros; sorry

/-- The left-derived factorization comparison is compatible with shifts. -/
@[stacks 05SE "left-derived factorization comparison shift compatibility"]
noncomputable instance facIso.homCommShift [IsSaturatedMultiplicativeSystem S] :
    NatTrans.CommShift (facIso F S).hom ℤ where
  shift_comm := by intros; sorry

end Shift

end Functor.LeftDerived.DefinedAt

end CategoryTheory
