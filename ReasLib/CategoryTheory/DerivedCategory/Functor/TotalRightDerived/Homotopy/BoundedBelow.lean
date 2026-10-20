/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Cohomology
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Total

/-!
# Bounded-below values of unbounded total right-derived functors

For an additive functor between abelian categories, this leaf compares the total right-derived
functor formed in the bounded-below derived category with the restriction of the unbounded total
right-derived functor.  The comparison is obtained from the universal property of right-derived
functors, so it is independent of resolutions and of the chosen localization model.

The functor-level comparison is constructed over the canonical localization category of
`HomotopyCategory.Plus.quasiIso A`.  Its value, cochain, and cohomology specializations are the
public API intended for downstream use.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Homotopy.BoundedBelow

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive]
variable [F.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]
variable [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
  (HomotopyCategory.quasiIso A (up ℤ))]

/-- The bounded-below homotopy functor, with its values included in the unbounded target derived
category. -/
@[stacks 05SA, stacks 05S9]
abbrev source : HomotopyCategory.Plus A ⥤ DerivedCategory B :=
  F.toBoundedBelowDerived ⋙ DerivedCategory.Plus.ι

/-- The bounded-below total right-derived model, with its values included in the unbounded target
derived category. -/
@[stacks 05SA, stacks 05S9]
abbrev boundedModel :
    (HomotopyCategory.Plus.quasiIso A).Localization ⥤ DerivedCategory B :=
  (F.toBoundedBelowDerived.totalRightDerived
      (HomotopyCategory.Plus.quasiIso A).Q
      (HomotopyCategory.Plus.quasiIso A)) ⋙
    DerivedCategory.Plus.ι

/-- The unit exhibiting the included bounded-below total right-derived model as a derived functor
of `source F`. -/
@[stacks 05SA, stacks 05S9]
noncomputable def boundedUnit :
    source F ⟶
      (HomotopyCategory.Plus.quasiIso A).Q ⋙ boundedModel F :=
  Functor.whiskerRight
      (F.toBoundedBelowDerived.totalRightDerivedUnit
        (HomotopyCategory.Plus.quasiIso A).Q
        (HomotopyCategory.Plus.quasiIso A))
      DerivedCategory.Plus.ι ≫
    (Functor.associator
      (HomotopyCategory.Plus.quasiIso A).Q
      (F.toBoundedBelowDerived.totalRightDerived
        (HomotopyCategory.Plus.quasiIso A).Q
        (HomotopyCategory.Plus.quasiIso A))
      DerivedCategory.Plus.ι).hom

/-- The included bounded-below model is a right-derived functor of the included bounded-below
homotopy functor. -/
@[stacks 05SA, stacks 05S9]
noncomputable instance boundedModelIsRightDerived :
    (boundedModel F).IsRightDerivedFunctor (boundedUnit F)
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- The restriction of the unbounded total right-derived functor to the bounded-below homotopy
category. -/
@[stacks 05SA, stacks 05S9]
abbrev unboundedSource : HomotopyCategory.Plus A ⥤ DerivedCategory B :=
  DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ⋙
    RightDerived.Homotopy.functor F

/-- The canonical comparison from termwise bounded-below application to the restriction of the
unbounded total right-derived functor. -/
@[stacks 05SA, stacks 05S9]
noncomputable def unboundedComparison : source F ⟶ unboundedSource F :=
  (Functor.toBoundedBelowDerived.compInclusionIso F).hom ≫
    Functor.whiskerLeft (HomotopyCategory.plus A).ι
      (RightDerived.Homotopy.unit F) ≫
    (Functor.associator
      (HomotopyCategory.plus A).ι DerivedCategory.Qh
      (RightDerived.Homotopy.functor F)).inv ≫
    (Functor.isoWhiskerRight
      (DerivedCategory.Plus.QhCompιIsoιCompQh A)
      (RightDerived.Homotopy.functor F)).inv ≫
    (Functor.associator DerivedCategory.Plus.Qh DerivedCategory.Plus.ι
      (RightDerived.Homotopy.functor F)).hom

/-- The bounded-below restriction of the unbounded total right-derived functor inverts
bounded-below quasi-isomorphisms. -/
@[stacks 05SA, stacks 05S9]
theorem unboundedSourceInverts :
    (HomotopyCategory.Plus.quasiIso A).IsInvertedBy (unboundedSource F) := sorry

/-- The lift of the bounded-below restriction of the unbounded total right-derived functor to the
canonical bounded-below localization category. -/
@[stacks 05SA, stacks 05S9]
noncomputable def unboundedModel :
    (HomotopyCategory.Plus.quasiIso A).Localization ⥤ DerivedCategory B :=
  Localization.lift (unboundedSource F) (unboundedSourceInverts F)
    (HomotopyCategory.Plus.quasiIso A).Q

/-- The right-derived unit of the localization lift of the unbounded model. -/
@[stacks 05SA, stacks 05S9]
noncomputable def unboundedUnit :
    source F ⟶
      (HomotopyCategory.Plus.quasiIso A).Q ⋙ unboundedModel F :=
  unboundedComparison F ≫
    (Localization.fac (unboundedSource F) (unboundedSourceInverts F)
      (HomotopyCategory.Plus.quasiIso A).Q).inv

/-- The localization lift of the unbounded model is a right-derived functor of the same source as
the included bounded-below model. -/
@[stacks 05SA, stacks 05S9]
noncomputable instance unboundedModelIsRightDerived :
    (unboundedModel F).IsRightDerivedFunctor (unboundedUnit F)
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- The canonical natural isomorphism from the included bounded-below total right-derived model
to the localization lift of the unbounded model. -/
@[stacks 05SA "bounded-below pointwise right-derived comparison", stacks 05S9]
noncomputable def modelIso : boundedModel F ≅ unboundedModel F :=
  (boundedModel F).rightDerivedUnique (unboundedModel F)
    (boundedUnit F) (unboundedUnit F) (HomotopyCategory.Plus.quasiIso A)

/-- The forward model comparison carries the bounded-below derived unit to the unbounded derived
unit. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem modelIso_fac :
    boundedUnit F ≫ Functor.whiskerLeft
        (HomotopyCategory.Plus.quasiIso A).Q (modelIso F).hom =
      unboundedUnit F := sorry

/-- The inverse model comparison carries the unbounded derived unit back to the bounded-below
derived unit. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem modelIso_inv_fac :
    unboundedUnit F ≫ Functor.whiskerLeft
        (HomotopyCategory.Plus.quasiIso A).Q (modelIso F).inv =
      boundedUnit F := sorry

/-- The canonical comparison at a bounded-below homotopy object, from the included
bounded-below total right-derived value to the unbounded total right-derived value. -/
@[stacks 05SA "bounded-below pointwise right-derived value", stacks 05S9]
noncomputable def valueIso (X : HomotopyCategory.Plus A) :
    (boundedModel F).obj ((HomotopyCategory.Plus.quasiIso A).Q.obj X) ≅
      (unboundedSource F).obj X :=
  (modelIso F).app ((HomotopyCategory.Plus.quasiIso A).Q.obj X) ≪≫
    (Localization.fac (unboundedSource F) (unboundedSourceInverts F)
      (HomotopyCategory.Plus.quasiIso A).Q).app X

/-- Naturality of the forward bounded-below value comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem valueIso_naturality {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y) :
    (boundedModel F).map ((HomotopyCategory.Plus.quasiIso A).Q.map f) ≫
        (valueIso F Y).hom =
      (valueIso F X).hom ≫ (unboundedSource F).map f := sorry

/-- Naturality of the inverse bounded-below value comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem valueIso_inv_naturality {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y) :
    (unboundedSource F).map f ≫ (valueIso F Y).inv =
      (valueIso F X).inv ≫
        (boundedModel F).map ((HomotopyCategory.Plus.quasiIso A).Q.map f) := sorry

/-- Conjugating the unbounded value map by the bounded-below comparison recovers the bounded
model map. -/
@[reassoc, stacks 05SA "source-map computation for bounded-below values", stacks 05S9]
theorem valueIso_source_map {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y) :
    (valueIso F X).hom ≫ (unboundedSource F).map f ≫ (valueIso F Y).inv =
      (boundedModel F).map ((HomotopyCategory.Plus.quasiIso A).Q.map f) := sorry

/-- Conjugating the bounded model map by the inverse bounded-below comparison recovers the
unbounded value map. -/
@[reassoc, stacks 05SA "target-map computation for bounded-below values", stacks 05S9]
theorem valueIso_target_map {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y) :
    (valueIso F X).inv ≫
        (boundedModel F).map ((HomotopyCategory.Plus.quasiIso A).Q.map f) ≫
      (valueIso F Y).hom =
      (unboundedSource F).map f := sorry

/-- The canonical bounded-below right-derived functor, with values included in the unbounded
target derived category. -/
@[stacks 05SA, stacks 05S9]
abbrev canonicalBoundedModel : DerivedCategory.Plus A ⥤ DerivedCategory B :=
  Functor.RightDerived.Bounded.functor F ⋙ DerivedCategory.Plus.ι

/-- The included canonical bounded-below unit, expressed over the public localization functor
`DerivedCategory.Plus.Qh`. -/
@[stacks 05SA, stacks 05S9]
noncomputable def canonicalBoundedUnit :
    source F ⟶ DerivedCategory.Plus.Qh ⋙ canonicalBoundedModel F :=
  Functor.whiskerRight (Functor.RightDerived.Bounded.unit F)
      DerivedCategory.Plus.ι ≫
    (Functor.associator DerivedCategory.Plus.Qh
      (Functor.RightDerived.Bounded.functor F) DerivedCategory.Plus.ι).hom

/-- The restriction of the unbounded total right-derived functor to the public bounded-below
derived category. -/
@[stacks 05SA, stacks 05S9]
abbrev canonicalUnboundedModel : DerivedCategory.Plus A ⥤ DerivedCategory B :=
  DerivedCategory.Plus.ι ⋙ RightDerived.Homotopy.functor F

/-- The unbounded comparison, reassociated as a derived unit over the public localization
functor `DerivedCategory.Plus.Qh`. -/
@[stacks 05SA, stacks 05S9]
noncomputable def canonicalUnboundedUnit :
    source F ⟶ DerivedCategory.Plus.Qh ⋙ canonicalUnboundedModel F :=
  unboundedComparison F ≫
    (Functor.associator DerivedCategory.Plus.Qh DerivedCategory.Plus.ι
      (RightDerived.Homotopy.functor F)).hom

/-- The included canonical bounded-below model is a right-derived functor over
`DerivedCategory.Plus.Qh`. -/
@[stacks 05SA, stacks 05S9]
noncomputable instance canonicalBoundedModelIsRightDerived :
    (canonicalBoundedModel F).IsRightDerivedFunctor (canonicalBoundedUnit F)
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- The restriction of the unbounded model is a right-derived functor over
`DerivedCategory.Plus.Qh`. -/
@[stacks 05SA, stacks 05S9]
noncomputable instance canonicalUnboundedModelIsRightDerived :
    (canonicalUnboundedModel F).IsRightDerivedFunctor (canonicalUnboundedUnit F)
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- The canonical natural isomorphism from the included bounded-below right-derived functor to
the restriction of the unbounded total right-derived functor. -/
@[stacks 05SA "canonical bounded-below right-derived comparison", stacks 05S9]
noncomputable def canonicalModelIso :
    canonicalBoundedModel F ≅ canonicalUnboundedModel F :=
  (canonicalBoundedModel F).rightDerivedUnique (canonicalUnboundedModel F)
    (canonicalBoundedUnit F) (canonicalUnboundedUnit F)
    (HomotopyCategory.Plus.quasiIso A)

/-- The canonical comparison at a bounded-below homotopy object, stated using the public
bounded-below derived category rather than a chosen localization model. -/
@[stacks 05SA "canonical bounded-below right-derived value", stacks 05S9]
noncomputable def canonicalValueIso (X : HomotopyCategory.Plus A) :
    DerivedCategory.Plus.ι.obj
        ((Functor.RightDerived.Bounded.functor F).obj
          (DerivedCategory.Plus.Qh.obj X)) ≅
      (unboundedSource F).obj X :=
  (canonicalModelIso F).app (DerivedCategory.Plus.Qh.obj X)

/-- Naturality of the forward canonical bounded-below value comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem canonicalValueIso_naturality
    {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y) :
    (canonicalBoundedModel F).map (DerivedCategory.Plus.Qh.map f) ≫
        (canonicalValueIso F Y).hom =
      (canonicalValueIso F X).hom ≫ (unboundedSource F).map f := sorry

/-- Naturality of the inverse canonical bounded-below value comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem canonicalValueIso_inv_naturality
    {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y) :
    (unboundedSource F).map f ≫ (canonicalValueIso F Y).inv =
      (canonicalValueIso F X).inv ≫
        (canonicalBoundedModel F).map (DerivedCategory.Plus.Qh.map f) := sorry

/-- Conjugating the unbounded value map by the canonical bounded-below comparison recovers the
canonical bounded model map. -/
@[reassoc, stacks 05SA "source-map computation for canonical bounded-below values", stacks 05S9]
theorem canonicalValueIso_source_map
    {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y) :
    (canonicalValueIso F X).hom ≫ (unboundedSource F).map f ≫
        (canonicalValueIso F Y).inv =
      (canonicalBoundedModel F).map (DerivedCategory.Plus.Qh.map f) := sorry

/-- Conjugating the canonical bounded model map by the inverse comparison recovers the unbounded
value map. -/
@[reassoc, stacks 05SA "target-map computation for canonical bounded-below values", stacks 05S9]
theorem canonicalValueIso_target_map
    {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y) :
    (canonicalValueIso F X).inv ≫
        (canonicalBoundedModel F).map (DerivedCategory.Plus.Qh.map f) ≫
      (canonicalValueIso F Y).hom =
      (unboundedSource F).map f := sorry

/-- The canonical comparison for a bounded-below cochain complex, with both sides expressed
through the public bounded-below and unbounded derived categories. -/
@[stacks 05SA "canonical bounded-below cochain right-derived value", stacks 05S9]
noncomputable def canonicalCochainValueIso (K : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.obj
        ((Functor.RightDerived.Bounded.functor F).obj
          (DerivedCategory.Plus.Qh.obj
            ((HomotopyCategory.Plus.quotient A).obj K))) ≅
      (RightDerived.Homotopy.cochainFunctor F).obj
        ((CochainComplex.Plus.ι A).obj K) :=
  canonicalValueIso F ((HomotopyCategory.Plus.quotient A).obj K) ≪≫
    (RightDerived.Homotopy.functor F).mapIso
      ((DerivedCategory.Plus.Qh.compInclusionIso A).app K)

/-- Naturality of the forward canonical cochain-level comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem canonicalCochainValueIso_naturality
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (canonicalBoundedModel F).map
          (DerivedCategory.Plus.Qh.map
            ((HomotopyCategory.Plus.quotient A).map f)) ≫
        (canonicalCochainValueIso F L).hom =
      (canonicalCochainValueIso F K).hom ≫
        (RightDerived.Homotopy.cochainFunctor F).map
          ((CochainComplex.Plus.ι A).map f) := sorry

/-- Naturality of the inverse canonical cochain-level comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem canonicalCochainValueIso_inv_naturality
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (RightDerived.Homotopy.cochainFunctor F).map
          ((CochainComplex.Plus.ι A).map f) ≫
        (canonicalCochainValueIso F L).inv =
      (canonicalCochainValueIso F K).inv ≫
        (canonicalBoundedModel F).map
          (DerivedCategory.Plus.Qh.map
            ((HomotopyCategory.Plus.quotient A).map f)) := sorry

/-- Conjugating the unbounded cochain map by the canonical comparison recovers the canonical
bounded-below cochain map. -/
@[reassoc, stacks 05SA "source-map computation for canonical bounded-below cochains", stacks 05S9]
theorem canonicalCochainValueIso_source_map
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (canonicalCochainValueIso F K).hom ≫
        (RightDerived.Homotopy.cochainFunctor F).map
          ((CochainComplex.Plus.ι A).map f) ≫
      (canonicalCochainValueIso F L).inv =
      (canonicalBoundedModel F).map
        (DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient A).map f)) := sorry

/-- Conjugating the canonical bounded-below cochain map by the inverse comparison recovers the
unbounded cochain map. -/
@[reassoc, stacks 05SA "target-map computation for canonical bounded-below cochains", stacks 05S9]
theorem canonicalCochainValueIso_target_map
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (canonicalCochainValueIso F K).inv ≫
        (canonicalBoundedModel F).map
          (DerivedCategory.Plus.Qh.map
            ((HomotopyCategory.Plus.quotient A).map f)) ≫
      (canonicalCochainValueIso F L).hom =
      (RightDerived.Homotopy.cochainFunctor F).map
        ((CochainComplex.Plus.ι A).map f) := sorry

/-- The canonical comparison for a bounded-below cochain complex, with the target expressed by
the ordinary unbounded cochain-level total right-derived functor. -/
@[stacks 05SA "bounded-below cochain right-derived value", stacks 05S9]
noncomputable def cochainValueIso (K : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.obj
        (Functor.RightDerived.Bounded.value F.toBoundedBelowDerived
          (HomotopyCategory.Plus.quasiIso A).Q K) ≅
      (RightDerived.Homotopy.cochainFunctor F).obj
        ((CochainComplex.Plus.ι A).obj K) :=
  valueIso F ((HomotopyCategory.Plus.quotient A).obj K) ≪≫
    (RightDerived.Homotopy.functor F).mapIso
      ((DerivedCategory.Plus.Qh.compInclusionIso A).app K)

/-- Naturality of the forward cochain-level bounded-below comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem cochainValueIso_naturality {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (boundedModel F).map
          ((HomotopyCategory.Plus.quasiIso A).Q.map
            ((HomotopyCategory.Plus.quotient A).map f)) ≫
        (cochainValueIso F L).hom =
      (cochainValueIso F K).hom ≫
        (RightDerived.Homotopy.cochainFunctor F).map
          ((CochainComplex.Plus.ι A).map f) := sorry

/-- Naturality of the inverse cochain-level bounded-below comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem cochainValueIso_inv_naturality {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (RightDerived.Homotopy.cochainFunctor F).map
          ((CochainComplex.Plus.ι A).map f) ≫
        (cochainValueIso F L).inv =
      (cochainValueIso F K).inv ≫
        (boundedModel F).map
          ((HomotopyCategory.Plus.quasiIso A).Q.map
            ((HomotopyCategory.Plus.quotient A).map f)) := sorry

/-- Conjugating the unbounded cochain map by the bounded-below comparison recovers the bounded
model cochain map. -/
@[reassoc, stacks 05SA "source-map computation for bounded-below cochains", stacks 05S9]
theorem cochainValueIso_source_map {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (cochainValueIso F K).hom ≫
        (RightDerived.Homotopy.cochainFunctor F).map
          ((CochainComplex.Plus.ι A).map f) ≫
      (cochainValueIso F L).inv =
      (boundedModel F).map
        ((HomotopyCategory.Plus.quasiIso A).Q.map
          ((HomotopyCategory.Plus.quotient A).map f)) := sorry

/-- Conjugating the bounded model cochain map by the inverse comparison recovers the unbounded
cochain map. -/
@[reassoc, stacks 05SA "target-map computation for bounded-below cochains", stacks 05S9]
theorem cochainValueIso_target_map {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (cochainValueIso F K).inv ≫
        (boundedModel F).map
          ((HomotopyCategory.Plus.quasiIso A).Q.map
            ((HomotopyCategory.Plus.quotient A).map f)) ≫
      (cochainValueIso F L).hom =
      (RightDerived.Homotopy.cochainFunctor F).map
        ((CochainComplex.Plus.ι A).map f) := sorry

/-- The degree-`n` cohomology comparison between bounded-below and unbounded total
right-derived values. -/
@[stacks 05SA "bounded-below pointwise right-derived cohomology", stacks 05S9]
noncomputable def cochainCohomologyIso (K : CochainComplex.Plus A) (n : ℤ) :
    Functor.RightDerived.Bounded.cohomology F
        (HomotopyCategory.Plus.quasiIso A).Q K n ≅
      RightDerived.Homotopy.cochainCohomology F
        ((CochainComplex.Plus.ι A).obj K) n :=
  (DerivedCategory.homologyFunctor B n).mapIso (cochainValueIso F K)

/-- Naturality of the forward bounded-below cohomology comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem cochainCohomologyIso_naturality
    {K L : CochainComplex.Plus A} (f : K ⟶ L) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).map
          ((F.toBoundedBelowDerived.totalRightDerived
            (HomotopyCategory.Plus.quasiIso A).Q
            (HomotopyCategory.Plus.quasiIso A)).map
              ((HomotopyCategory.Plus.quasiIso A).Q.map
                ((HomotopyCategory.Plus.quotient A).map f))) ≫
        (cochainCohomologyIso F L n).hom =
      (cochainCohomologyIso F K n).hom ≫
        RightDerived.Homotopy.cochainCohomologyMap F
          ((CochainComplex.Plus.ι A).map f) n := sorry

/-- Naturality of the inverse bounded-below cohomology comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem cochainCohomologyIso_inv_naturality
    {K L : CochainComplex.Plus A} (f : K ⟶ L) (n : ℤ) :
    RightDerived.Homotopy.cochainCohomologyMap F
          ((CochainComplex.Plus.ι A).map f) n ≫
        (cochainCohomologyIso F L n).inv =
      (cochainCohomologyIso F K n).inv ≫
        (DerivedCategory.Plus.homologyFunctor B n).map
          ((F.toBoundedBelowDerived.totalRightDerived
            (HomotopyCategory.Plus.quasiIso A).Q
            (HomotopyCategory.Plus.quasiIso A)).map
              ((HomotopyCategory.Plus.quasiIso A).Q.map
                ((HomotopyCategory.Plus.quotient A).map f))) := sorry

/-- Conjugating the unbounded cochain-cohomology map by the comparison recovers the
bounded-below cohomology map. -/
@[reassoc, stacks 05SA "source-map computation for bounded-below cohomology", stacks 05S9]
theorem cochainCohomologyIso_source_map
    {K L : CochainComplex.Plus A} (f : K ⟶ L) (n : ℤ) :
    (cochainCohomologyIso F K n).hom ≫
        RightDerived.Homotopy.cochainCohomologyMap F
          ((CochainComplex.Plus.ι A).map f) n ≫
      (cochainCohomologyIso F L n).inv =
      (DerivedCategory.Plus.homologyFunctor B n).map
        ((F.toBoundedBelowDerived.totalRightDerived
          (HomotopyCategory.Plus.quasiIso A).Q
          (HomotopyCategory.Plus.quasiIso A)).map
            ((HomotopyCategory.Plus.quasiIso A).Q.map
              ((HomotopyCategory.Plus.quotient A).map f))) := sorry

/-- Conjugating the bounded-below cohomology map by the inverse comparison recovers the
unbounded cochain-cohomology map. -/
@[reassoc, stacks 05SA "target-map computation for bounded-below cohomology", stacks 05S9]
theorem cochainCohomologyIso_target_map
    {K L : CochainComplex.Plus A} (f : K ⟶ L) (n : ℤ) :
    (cochainCohomologyIso F K n).inv ≫
        (DerivedCategory.Plus.homologyFunctor B n).map
          ((F.toBoundedBelowDerived.totalRightDerived
            (HomotopyCategory.Plus.quasiIso A).Q
            (HomotopyCategory.Plus.quasiIso A)).map
              ((HomotopyCategory.Plus.quasiIso A).Q.map
                ((HomotopyCategory.Plus.quotient A).map f))) ≫
      (cochainCohomologyIso F L n).hom =
      RightDerived.Homotopy.cochainCohomologyMap F
        ((CochainComplex.Plus.ι A).map f) n := sorry

variable [F.toBoundedBelowDerived.HasPointwiseRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]

/-- The pointwise bounded-below right-derived value of a cochain complex, included in the
unbounded target, is canonically isomorphic to its unbounded total right-derived value. -/
@[stacks 05SA "bounded-below pointwise cochain right-derived value", stacks 05S9]
noncomputable def pointwiseCochainValueIso (K : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.obj
        (CategoryTheory.Functor.RightDerived.Value.obj F.toBoundedBelowDerived
          (HomotopyCategory.Plus.quasiIso A)
          ((HomotopyCategory.Plus.quotient A).obj K)) ≅
      (RightDerived.Homotopy.cochainFunctor F).obj
        ((CochainComplex.Plus.ι A).obj K) :=
  DerivedCategory.Plus.ι.mapIso
      (CategoryTheory.Functor.RightDerived.Value.totalIso F.toBoundedBelowDerived
        (HomotopyCategory.Plus.quasiIso A)
        ((HomotopyCategory.Plus.quotient A).obj K)).symm ≪≫
    cochainValueIso F K

/-- Naturality of the forward pointwise cochain-value comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem pointwiseCochainValueIso_naturality
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map
          (CategoryTheory.Functor.RightDerived.Value.map F.toBoundedBelowDerived
            (HomotopyCategory.Plus.quasiIso A)
            ((HomotopyCategory.Plus.quotient A).map f)) ≫
        (pointwiseCochainValueIso F L).hom =
      (pointwiseCochainValueIso F K).hom ≫
        (RightDerived.Homotopy.cochainFunctor F).map
          ((CochainComplex.Plus.ι A).map f) := sorry

/-- Naturality of the inverse pointwise cochain-value comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem pointwiseCochainValueIso_inv_naturality
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (RightDerived.Homotopy.cochainFunctor F).map
          ((CochainComplex.Plus.ι A).map f) ≫
        (pointwiseCochainValueIso F L).inv =
      (pointwiseCochainValueIso F K).inv ≫
        DerivedCategory.Plus.ι.map
          (CategoryTheory.Functor.RightDerived.Value.map F.toBoundedBelowDerived
            (HomotopyCategory.Plus.quasiIso A)
            ((HomotopyCategory.Plus.quotient A).map f)) := sorry

/-- The cohomology of a pointwise bounded-below right-derived value is canonically isomorphic to
the cohomology of the unbounded total right-derived cochain value. -/
@[stacks 05SA "bounded-below pointwise cochain right-derived cohomology", stacks 05S9]
noncomputable def pointwiseCochainCohomologyIso
    (K : CochainComplex.Plus A) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).obj
        (CategoryTheory.Functor.RightDerived.Value.obj F.toBoundedBelowDerived
          (HomotopyCategory.Plus.quasiIso A)
          ((HomotopyCategory.Plus.quotient A).obj K)) ≅
      RightDerived.Homotopy.cochainCohomology F
        ((CochainComplex.Plus.ι A).obj K) n :=
  (DerivedCategory.Plus.homologyFunctor B n).mapIso
      (CategoryTheory.Functor.RightDerived.Value.totalIso F.toBoundedBelowDerived
        (HomotopyCategory.Plus.quasiIso A)
        ((HomotopyCategory.Plus.quotient A).obj K)).symm ≪≫
    cochainCohomologyIso F K n

/-- Naturality of the forward pointwise cochain-cohomology comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem pointwiseCochainCohomologyIso_naturality
    {K L : CochainComplex.Plus A} (f : K ⟶ L) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).map
          (CategoryTheory.Functor.RightDerived.Value.map F.toBoundedBelowDerived
            (HomotopyCategory.Plus.quasiIso A)
            ((HomotopyCategory.Plus.quotient A).map f)) ≫
        (pointwiseCochainCohomologyIso F L n).hom =
      (pointwiseCochainCohomologyIso F K n).hom ≫
        RightDerived.Homotopy.cochainCohomologyMap F
          ((CochainComplex.Plus.ι A).map f) n := sorry

/-- Naturality of the inverse pointwise cochain-cohomology comparison. -/
@[reassoc, stacks 05SA, stacks 05S9]
theorem pointwiseCochainCohomologyIso_inv_naturality
    {K L : CochainComplex.Plus A} (f : K ⟶ L) (n : ℤ) :
    RightDerived.Homotopy.cochainCohomologyMap F
          ((CochainComplex.Plus.ι A).map f) n ≫
        (pointwiseCochainCohomologyIso F L n).inv =
      (pointwiseCochainCohomologyIso F K n).inv ≫
        (DerivedCategory.Plus.homologyFunctor B n).map
          (CategoryTheory.Functor.RightDerived.Value.map F.toBoundedBelowDerived
            (HomotopyCategory.Plus.quasiIso A)
            ((HomotopyCategory.Plus.quotient A).map f)) := sorry

/-- Conjugating the unbounded cochain-cohomology map by the pointwise comparison recovers the
pointwise bounded-below cohomology map. -/
@[reassoc, stacks 05SA "source-map computation for pointwise bounded-below cohomology", stacks 05S9]
theorem pointwiseCochainCohomologyIso_source_map
    {K L : CochainComplex.Plus A} (f : K ⟶ L) (n : ℤ) :
    (pointwiseCochainCohomologyIso F K n).hom ≫
        RightDerived.Homotopy.cochainCohomologyMap F
          ((CochainComplex.Plus.ι A).map f) n ≫
      (pointwiseCochainCohomologyIso F L n).inv =
      (DerivedCategory.Plus.homologyFunctor B n).map
        (CategoryTheory.Functor.RightDerived.Value.map F.toBoundedBelowDerived
          (HomotopyCategory.Plus.quasiIso A)
          ((HomotopyCategory.Plus.quotient A).map f)) := sorry

/-- Conjugating the pointwise bounded-below cohomology map by the inverse comparison recovers the
unbounded cochain-cohomology map. -/
@[reassoc, stacks 05SA "target-map computation for pointwise bounded-below cohomology", stacks 05S9]
theorem pointwiseCochainCohomologyIso_target_map
    {K L : CochainComplex.Plus A} (f : K ⟶ L) (n : ℤ) :
    (pointwiseCochainCohomologyIso F K n).inv ≫
        (DerivedCategory.Plus.homologyFunctor B n).map
          (CategoryTheory.Functor.RightDerived.Value.map F.toBoundedBelowDerived
            (HomotopyCategory.Plus.quasiIso A)
            ((HomotopyCategory.Plus.quotient A).map f)) ≫
      (pointwiseCochainCohomologyIso F L n).hom =
      RightDerived.Homotopy.cochainCohomologyMap F
        ((CochainComplex.Plus.ι A).map f) n := sorry

end CategoryTheory.Functor.RightDerived.Homotopy.BoundedBelow
