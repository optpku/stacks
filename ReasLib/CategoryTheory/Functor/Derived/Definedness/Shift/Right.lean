module

public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Right
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Shift.Right
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Iso
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Shift

@[expose] public section

/-!
# Shifts on the Domain of a Pointwise Right-Derived Functor

The domain on which pointwise right-derived values exist is shift-stable.  This leaf equips the
restricted functor and its localization factorization with their canonical shift comparisons,
without assuming additive or triangulated structures.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Localization MorphismProperty ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasShift D ℤ] [HasShift D' ℤ]
  (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]

namespace Functor.RightDerived.Definedness

namespace Domain

/-- The source of the inclusion's shift comparison is pointwise right-derived-defined.  The
functor-composite form is intentional: it is the form exposed by `commShiftIso`. -/
@[stacks 05SE "right-derived definedness at the source of the inclusion shift comparison"]
instance inclusionShiftSourceHasPointwise (X : Domain F S) (n : ℤ) :
    F.HasPointwiseRightDerivedFunctorAt S
      ((shiftFunctor (Domain F S) n ⋙ (property F S).ι).obj X) := sorry

/-- The target of the inclusion's shift comparison is pointwise right-derived-defined.  This
bridge exposes ambient shift stability in the functor-composite form used by `commShiftIso`. -/
@[stacks 05SE "right-derived definedness at the target of the inclusion shift comparison"]
instance inclusionShiftTargetHasPointwise (X : Domain F S) (n : ℤ) :
    F.HasPointwiseRightDerivedFunctorAt S
      (((property F S).ι ⋙ shiftFunctor D n).obj X) := sorry

end Domain

namespace functor

/-- The component of the shift comparison for the restricted right-derived functor.  It first
uses the shift comparison of the full-subcategory inclusion and then the pointwise derived-value
shift comparison. -/
@[stacks 05SE "right-derived domain functor shift component"]
noncomputable def shiftIsoApp (X : Domain F S) (n : ℤ) :
    (functor F S).obj ((shiftFunctor (Domain F S) n).obj X) ≅
      ((functor F S).obj X)⟦n⟧ :=
  CategoryTheory.Functor.RightDerived.Value.mapIso
      F S (((property F S).ι.commShiftIso n).app X) ≪≫
    Functor.RightDerived.Value.Shift.valueIso F S X.obj n

/-- Naturality of the componentwise shift comparison for the restricted right-derived functor. -/
@[stacks 05SE "right-derived domain functor shift naturality"]
theorem shiftIsoApp_naturality (n : ℤ) {X Y : Domain F S} (f : X ⟶ Y) :
    (functor F S).map ((shiftFunctor (Domain F S) n).map f) ≫
        (shiftIsoApp F S Y n).hom =
      (shiftIsoApp F S X n).hom ≫
        (shiftFunctor D' n).map ((functor F S).map f) := sorry

/-- The canonical shift comparison for the restricted right-derived functor. -/
@[stacks 05SE "right-derived domain functor shift comparison"]
noncomputable def shiftIso (n : ℤ) :
    shiftFunctor (Domain F S) n ⋙ functor F S ≅
      functor F S ⋙ shiftFunctor D' n :=
  NatIso.ofComponents (fun X ↦ shiftIsoApp F S X n)
    (fun f ↦ shiftIsoApp_naturality F S n f)

/-- The restricted right-derived shift comparison at zero is the canonical zero comparison. -/
@[stacks 05SE "right-derived domain functor zero-shift coherence"]
theorem shiftIso_zero :
    shiftIso F S 0 = Functor.CommShift.isoZero (functor F S) ℤ := sorry

/-- The restricted right-derived shift comparison is coherent with addition of shifts. -/
@[stacks 05SE "right-derived domain functor additive-shift coherence"]
theorem shiftIso_add (a b : ℤ) :
    shiftIso F S (a + b) =
      Functor.CommShift.isoAdd (shiftIso F S a) (shiftIso F S b) := sorry

/-- The restricted pointwise right-derived functor commutes with integer shifts. -/
@[stacks 05SE]
noncomputable instance commShift : (functor F S).CommShift ℤ where
  commShiftIso := shiftIso F S
  commShiftIso_zero := shiftIso_zero F S
  commShiftIso_add := shiftIso_add F S

/-- The forward shift comparison of the restricted right-derived functor is the inclusion-shift
transport followed by the raw pointwise shift comparison. -/
@[simp, stacks 05SE]
theorem commShiftIso_hom_app (X : Domain F S) (n : ℤ) :
    ((functor F S).commShiftIso n).hom.app X =
      CategoryTheory.Functor.RightDerived.Value.map F S (((property F S).ι.commShiftIso n).hom.app X) ≫
        (Functor.RightDerived.Value.Shift.valueIso F S X.obj n).hom := sorry

/-- The inverse shift comparison of the restricted right-derived functor is the inverse raw
pointwise comparison followed by transport along the inverse inclusion-shift comparison. -/
@[simp, stacks 05SE]
theorem commShiftIso_inv_app (X : Domain F S) (n : ℤ) :
    ((functor F S).commShiftIso n).inv.app X =
      (Functor.RightDerived.Value.Shift.valueIso F S X.obj n).inv ≫
        CategoryTheory.Functor.RightDerived.Value.map F S (((property F S).ι.commShiftIso n).inv.app X) := sorry

end functor

namespace localizationFactorization

/-- The localized right-derived factorization commutes with shifts. -/
@[stacks 05SE]
noncomputable instance commShift [S.RespectsIso] :
    (localizationFactorization F S).CommShift ℤ :=
  Functor.commShiftOfLocalization (system F S).Q (system F S) ℤ
    (functor F S) (localizationFactorization F S)

/-- The forward localized shift comparison on an object in the image of the localization
functor, expressed through the canonical factorization comparison. -/
@[simp, stacks 05SE]
theorem commShiftIso_hom_app_Q [S.RespectsIso] (X : Domain F S) (n : ℤ) :
    ((localizationFactorization F S).commShiftIso n).hom.app ((system F S).Q.obj X) =
      (localizationFactorization F S).map (((system F S).Q.commShiftIso n).inv.app X) ≫
        (facIso F S).hom.app (X⟦n⟧) ≫
          ((functor F S).commShiftIso n).hom.app X ≫
            (shiftFunctor D' n).map ((facIso F S).inv.app X) := sorry

/-- The inverse localized shift comparison on an object in the image of the localization
functor, expressed through the canonical factorization comparison. -/
@[simp, stacks 05SE]
theorem commShiftIso_inv_app_Q [S.RespectsIso] (X : Domain F S) (n : ℤ) :
    ((localizationFactorization F S).commShiftIso n).inv.app ((system F S).Q.obj X) =
      (shiftFunctor D' n).map ((facIso F S).hom.app X) ≫
        ((functor F S).commShiftIso n).inv.app X ≫
          (facIso F S).inv.app (X⟦n⟧) ≫
            (localizationFactorization F S).map
              (((system F S).Q.commShiftIso n).hom.app X) := sorry

end localizationFactorization

namespace facIso

/-- The canonical right-derived factorization comparison is compatible with shifts. -/
@[stacks 05SE]
noncomputable instance homCommShift [S.RespectsIso] :
    NatTrans.CommShift (facIso F S).hom ℤ :=
  (inferInstance : NatTrans.CommShift
    (Localization.Lifting.iso (system F S).Q (system F S) (functor F S)
      (localizationFactorization F S)).hom ℤ)

end facIso



end Functor.RightDerived.Definedness

end CategoryTheory
