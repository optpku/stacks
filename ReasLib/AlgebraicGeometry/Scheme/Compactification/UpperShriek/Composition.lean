/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.PlusModel
public import ReasLib.CategoryTheory.Adjunction.BaseChange.HorizontalComposition
public import ReasLib.CategoryTheory.Adjunction.BaseChange.VerticalComposition

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Scheme.Compactification
open Compactification.Of
open Scheme.DerivedQCoh

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Compactification.Of

/-- The ambient scheme of a fixed-interior compactification. -/
abbrev ambient {S : Scheme.{u}} {X : Over S} (P : Of S X) : Scheme.{u} :=
  P.obj.right.left

/-- The proper ambient morphism of a fixed-interior compactification. -/
abbrev ambientMorphism {S : Scheme.{u}} {X : Over S} (P : Of S X) : ambient P ⟶ S :=
  P.obj.right.hom

/-- The interior map of the compactification obtained by composing two compatible
compactifications is a morphism over the final base. -/
theorem compInterior_fac
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P_g : Of Z.obj.left (Over.mk g.hom.left))
    (P_bar : Of P_g.obj.right.left (Over.mk (f.hom.left ≫ ι P_g))) :
    ι P_bar ≫ (P_bar.obj.right.hom ≫ P_g.obj.right.hom) = (f ≫ g).hom.left := sorry

/-- The interior morphism over `Z` used to compose two compatible compactifications. -/
noncomputable def compInterior
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P_g : Of Z.obj.left (Over.mk g.hom.left))
    (P_bar : Of P_g.obj.right.left (Over.mk (f.hom.left ≫ ι P_g))) :
    Over.mk (f ≫ g).hom.left ⟶
      Over.mk (P_bar.obj.right.hom ≫ P_g.obj.right.hom) :=
  Over.homMk (ι P_bar) (compInterior_fac f g P_g P_bar)

/-- The underlying scheme map of `compInterior` is the chosen interior immersion. -/
theorem compInterior_left
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P_g : Of Z.obj.left (Over.mk g.hom.left))
    (P_bar : Of P_g.obj.right.left (Over.mk (f.hom.left ≫ ι P_g))) :
    (compInterior f g P_g P_bar).left = ι P_bar := sorry

/-- The composite compactification's interior map is an open immersion. -/
instance instCompInteriorIsOpenImmersion
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P_g : Of Z.obj.left (Over.mk g.hom.left))
    (P_bar : Of P_g.obj.right.left (Over.mk (f.hom.left ≫ ι P_g))) :
    IsOpenImmersion (compInterior f g P_g P_bar).left := sorry

/-- The composite compactification's interior map is quasi-compact. -/
instance instCompInteriorQuasiCompact
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P_g : Of Z.obj.left (Over.mk g.hom.left))
    (P_bar : Of P_g.obj.right.left (Over.mk (f.hom.left ≫ ι P_g))) :
    QuasiCompact (compInterior f g P_g P_bar).left := sorry

/-- The composite of the two proper ambient morphisms is proper over the final base. -/
theorem compAmbient_isProper
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P_g : Of Z.obj.left (Over.mk g.hom.left))
    (P_bar : Of P_g.obj.right.left (Over.mk (f.hom.left ≫ ι P_g))) :
    IsProper (P_bar.obj.right.hom ≫ P_g.obj.right.hom) := sorry

/-- The compactification of `f ≫ g` obtained by composing the proper ambient morphisms of
`P_bar` and `P_g`. -/
@[reducible]
noncomputable def comp
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P_g : Of Z.obj.left (Over.mk g.hom.left))
    (P_bar : Of P_g.obj.right.left (Over.mk (f.hom.left ≫ ι P_g))) :
    Of Z.obj.left (Over.mk (f ≫ g).hom.left) :=
  @Of.mk Z.obj.left _ (Over.mk (P_bar.obj.right.hom ≫ P_g.obj.right.hom))
    (compInterior f g P_g P_bar) (instCompInteriorIsOpenImmersion f g P_g P_bar)
    (instCompInteriorQuasiCompact f g P_g P_bar) (compAmbient_isProper f g P_g P_bar)

/-- The interior immersion of the composite compactification is the interior immersion of
`P_bar`. -/
theorem comp_ι
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P_g : Of Z.obj.left (Over.mk g.hom.left))
    (P_bar : Of P_g.obj.right.left (Over.mk (f.hom.left ≫ ι P_g))) :
    ι (comp f g P_g P_bar) = (compInterior f g P_g P_bar).left := sorry

/-- A coherent family of upper-shriek comparisons between compactifications of one
finite-type separated morphism. -/
structure UpperShriekComparisonSystem
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) where
  /-- The chosen bounded-below right-adjoint model for every compactification. -/
  model : (P : Of Y.obj.left (Over.mk f.hom.left)) →
    DerivedQCoh.PlusRightAdjoint (ambientMorphism P)
  /-- The functorial comparison object used to relate compactifications. -/
  comparison : Of Y.obj.left (Over.mk f.hom.left) ⥤
    (DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus X.obj.left)
  /-- Identification of the comparison object with the upper-shriek model. -/
  modelIso : ∀ P, comparison.obj P ≅ upperShriek f P (model P).plus
  /-- Comparison maps from dense interiors are invertible. -/
  comparisonIsIso : ∀ {P Q} (h : P ⟶ Q),
    IsDominant (ι P) → IsIso (comparison.map h)

namespace UpperShriekComparisonSystem

/-- Construct a coherent compactification-comparison system from its models,
comparison functor, identifications, and invertibility law. -/
def of
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} {f : X ⟶ Y}
    (model : (P : Of Y.obj.left (Over.mk f.hom.left)) →
      DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    (comparison : Of Y.obj.left (Over.mk f.hom.left) ⥤
      (DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus X.obj.left))
    (modelIso : ∀ P, comparison.obj P ≅ upperShriek f P (model P).plus)
    (comparisonIsIso : ∀ {P Q} (h : P ⟶ Q),
      IsDominant (ι P) → IsIso (comparison.map h)) :
    UpperShriekComparisonSystem f where
  model := model
  comparison := comparison
  modelIso := modelIso
  comparisonIsIso := comparisonIsIso

/-- The canonical upper-shriek comparison between two compactifications and two chosen
bounded-below right-adjoint models. -/
noncomputable def iso
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} {f : X ⟶ Y}
    (H : UpperShriekComparisonSystem f)
    (P Q : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    (B : DerivedQCoh.PlusRightAdjoint (ambientMorphism Q)) :
    upperShriek f P A.plus ≅ upperShriek f Q B.plus :=
  Functor.isoWhiskerRight (A.iso (H.model P))
      (@DerivedQCoh.OpenImmersion.pullbackPlus _ _ (ι P)
        P.property.isOpenImmersion) ≪≫
    upperShriekIso f (fun R ↦ (H.model R).right)
      (fun R ↦ (H.model R).adjunction) (fun R ↦ (H.model R).plus)
      (fun R ↦ (H.model R).compatibility) H.comparison H.modelIso
      H.comparisonIsIso P Q ≪≫
    Functor.isoWhiskerRight ((H.model Q).iso B)
      (@DerivedQCoh.OpenImmersion.pullbackPlus _ _ (ι Q)
        Q.property.isOpenImmersion)

end UpperShriekComparisonSystem

/-- A compatible choice of compactifications and bounded-below right-adjoint models used
to represent upper shriek for a composable pair. -/
structure UpperShriekCompChoice
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z) where
  /-- A compactification of `f`. -/
  P_f : Of Y.obj.left (Over.mk f.hom.left)
  /-- A compactification of `g`. -/
  P_g : Of Z.obj.left (Over.mk g.hom.left)
  /-- A compactification of `f` after the open immersion of `P_g`. -/
  P_bar : Of (ambient P_g) (Over.mk (f.hom.left ≫ ι P_g))
  /-- The comparison map between the two ambient compactifications of `f`. -/
  k : ambient P_f ⟶ ambient P_bar
  /-- The comparison map gives the cartesian square used for open base change. -/
  isPullback : IsPullback k (ambientMorphism P_f) (ambientMorphism P_bar) (ι P_g)
  /-- The comparison map agrees with the two chosen open interiors. -/
  interior_fac : ι P_f ≫ k = ι P_bar
  /-- A bounded-below right-adjoint model for the proper part of `P_f`. -/
  A_f : DerivedQCoh.PlusRightAdjoint (ambientMorphism P_f)
  /-- A bounded-below right-adjoint model for the proper part of `P_g`. -/
  A_g : DerivedQCoh.PlusRightAdjoint (ambientMorphism P_g)
  /-- A bounded-below right-adjoint model for the proper part of `P_bar`. -/
  A_bar : DerivedQCoh.PlusRightAdjoint (ambientMorphism P_bar)
  /-- A bounded-below right-adjoint model for the composed compactification. -/
  A_fg : DerivedQCoh.PlusRightAdjoint (ambientMorphism (comp f g P_g P_bar))

namespace UpperShriekCompChoice

/-- Construct a complete compatible choice from its compactifications, comparison square,
and bounded-below right-adjoint models. -/
def of
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (P_f : Of Y.obj.left (Over.mk f.hom.left))
    (P_g : Of Z.obj.left (Over.mk g.hom.left))
    (P_bar : Of (ambient P_g) (Over.mk (f.hom.left ≫ ι P_g)))
    (k : ambient P_f ⟶ ambient P_bar)
    (isPullback : IsPullback k (ambientMorphism P_f) (ambientMorphism P_bar) (ι P_g))
    (interior_fac : ι P_f ≫ k = ι P_bar)
    (A_f : DerivedQCoh.PlusRightAdjoint (ambientMorphism P_f))
    (A_g : DerivedQCoh.PlusRightAdjoint (ambientMorphism P_g))
    (A_bar : DerivedQCoh.PlusRightAdjoint (ambientMorphism P_bar))
    (A_fg : DerivedQCoh.PlusRightAdjoint (ambientMorphism (comp f g P_g P_bar))) :
    UpperShriekCompChoice f g where
  P_f := P_f
  P_g := P_g
  P_bar := P_bar
  k := k
  isPullback := isPullback
  interior_fac := interior_fac
  A_f := A_f
  A_g := A_g
  A_bar := A_bar
  A_fg := A_fg

/-- Pullback along a factored morphism agrees with iterated pullback. -/
noncomputable def pullbackCompIsoOfEq
    {W X Y : Scheme.{u}} (i : W ⟶ X) (k : X ⟶ Y) (j : W ⟶ Y)
    (h : i ≫ k = j) :
    DerivedQCoh.pullback k ⋙ DerivedQCoh.pullback i ≅ DerivedQCoh.pullback j :=
  DerivedQCoh.pullbackCompIso i k
      (RingedSpace.modulePullbackDerived.compComparison_isIso i.toShHom k.toShHom) ≪≫
    eqToIso (congrArg DerivedQCoh.pullback h)

/-- The ambient comparison from the open part of `P_bar` to the iterated pullback through
the cartesian comparison map. -/
noncomputable def sourceCompatibility
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (C : UpperShriekCompChoice f g) :
    (C.A_bar.plus ⋙ DerivedQCoh.OpenImmersion.pullbackPlus (ι C.P_bar)) ⋙
        DerivedCategory.Plus.CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty X.obj.left.toRingedSpace) ≅
      (DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty (ambient C.P_g).toRingedSpace) ⋙
        C.A_bar.right) ⋙
          ((DerivedQCoh.pullback C.k ⋙ DerivedQCoh.pullback (ι C.P_f)) ⋙
            DerivedQCoh.inclusion X.obj.left) :=
  C.A_bar.openRestrictionAmbientIso (ι C.P_bar) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight
        (pullbackCompIsoOfEq (ι C.P_f) C.k (ι C.P_bar) C.interior_fac).symm
        (DerivedQCoh.inclusion X.obj.left))

/-- The ambient comparison from the iterated open restriction of `g ! ⋙ f !` to the
corresponding unbounded pullbacks and right adjoints. -/
noncomputable def targetCompatibility
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (C : UpperShriekCompChoice f g) :
    (DerivedQCoh.OpenImmersion.pullbackPlus (ι C.P_g) ⋙
        upperShriek f C.P_f C.A_f.plus) ⋙
        DerivedCategory.Plus.CohomologyIn.ambient
          (RingedSpace.quasiCoherentModuleProperty X.obj.left.toRingedSpace) ≅
      (DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty (ambient C.P_g).toRingedSpace) ⋙
        DerivedQCoh.pullback (ι C.P_g)) ⋙
          (C.A_f.right ⋙
            (DerivedQCoh.pullback (ι C.P_f) ⋙ DerivedQCoh.inclusion X.obj.left)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedQCoh.OpenImmersion.pullbackPlus (ι C.P_g))
      (C.A_f.openRestrictionAmbientIso (ι C.P_f)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (DerivedQCoh.OpenImmersion.pullbackPlusRestrictionIso (ι C.P_g)) _

/-- The bounded-below exceptional base-change comparison, whiskered by the final open
restriction in the compactification of `f`. -/
noncomputable def baseChangeCompatibility
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (C : UpperShriekCompChoice f g) :
    (DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty (ambient C.P_g).toRingedSpace) ⋙
        C.A_bar.right) ⋙
          ((DerivedQCoh.pullback C.k ⋙ DerivedQCoh.pullback (ι C.P_f)) ⋙
            DerivedQCoh.inclusion X.obj.left) ≅
      (DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty (ambient C.P_g).toRingedSpace) ⋙
        DerivedQCoh.pullback (ι C.P_g)) ⋙
          (C.A_f.right ⋙
            (DerivedQCoh.pullback (ι C.P_f) ⋙ DerivedQCoh.inclusion X.obj.left)) :=
  let kIsOpen : IsOpenImmersion C.k :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback C.isPullback.flip
      C.P_g.property.isOpenImmersion
  let rest := DerivedQCoh.pullback (ι C.P_f) ⋙ DerivedQCoh.inclusion X.obj.left
  let sourceReassoc :
      (DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty (ambient C.P_g).toRingedSpace) ⋙
          C.A_bar.right) ⋙ ((DerivedQCoh.pullback C.k ⋙
            DerivedQCoh.pullback (ι C.P_f)) ⋙ DerivedQCoh.inclusion X.obj.left) ≅
        (DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty (ambient C.P_g).toRingedSpace) ⋙
          (C.A_bar.right ⋙ DerivedQCoh.pullback C.k)) ⋙ rest :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm) _ ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
      Functor.associator _ _ _
  let targetReassoc :
      (DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty (ambient C.P_g).toRingedSpace) ⋙
          (DerivedQCoh.pullback (ι C.P_g) ⋙ C.A_f.right)) ⋙ rest ≅
        (DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty (ambient C.P_g).toRingedSpace) ⋙
          DerivedQCoh.pullback (ι C.P_g)) ⋙ (C.A_f.right ⋙ rest) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm
  sourceReassoc ≪≫
    Functor.isoWhiskerRight
      (@DerivedQCoh.PlusRightAdjoint.openBaseChangeIso
        _ _ _ _ _ _ _ _ _ _ _ _ C.k (ambientMorphism C.P_f)
        (ambientMorphism C.P_bar) (ι C.P_g) _ _ C.P_g.property.isOpenImmersion
        kIsOpen C.isPullback C.A_bar C.A_f) rest ≪≫
    targetReassoc

/-- The canonical bounded-below open-base-change comparison attached to a complete
compactification choice. -/
noncomputable def openComparison
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (C : UpperShriekCompChoice f g) :
    C.A_bar.plus ⋙ DerivedQCoh.OpenImmersion.pullbackPlus (ι C.P_bar) ≅
      DerivedQCoh.OpenImmersion.pullbackPlus (ι C.P_g) ⋙
        upperShriek f C.P_f C.A_f.plus :=
  DerivedQCoh.Plus.isoOfAmbientIso _ _
    (C.sourceCompatibility ≪≫ C.baseChangeCompatibility ≪≫ C.targetCompatibility.symm)

/-- Assemble upper-shriek composition from the canonical proper-composition and
bounded-below open-base-change comparisons. -/
noncomputable def compIso
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g) :
    upperShriek (f ≫ g) (comp f g C.P_g C.P_bar) C.A_fg.plus ≅
      upperShriek g C.P_g C.A_g.plus ⋙ upperShriek f C.P_f C.A_f.plus :=
  let A_comp := DerivedQCoh.PlusRightAdjoint.comp
    (ambientMorphism C.P_bar) (ambientMorphism C.P_g) C.A_bar C.A_g
  Functor.isoWhiskerRight (DerivedQCoh.PlusRightAdjoint.iso C.A_fg A_comp)
      (@DerivedQCoh.OpenImmersion.pullbackPlus _ _ (ι C.P_bar)
        C.P_bar.property.isOpenImmersion) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft C.A_g.plus C.openComparison ≪≫
    (Functor.associator _ _ _).symm

/-- The forward map of `UpperShriekCompChoice.compIso` is the composite of the
right-adjoint uniqueness, associativity, and open-base-change comparisons. -/
theorem compIso_hom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g) :
    (C.compIso f g).hom =
      (Functor.isoWhiskerRight
        (DerivedQCoh.PlusRightAdjoint.iso C.A_fg
          (DerivedQCoh.PlusRightAdjoint.comp (ambientMorphism C.P_bar)
            (ambientMorphism C.P_g) C.A_bar C.A_g))
        (@DerivedQCoh.OpenImmersion.pullbackPlus _ _ (ι C.P_bar)
          C.P_bar.property.isOpenImmersion)).hom ≫
        (Functor.associator _ _ _).hom ≫
        (Functor.isoWhiskerLeft C.A_g.plus C.openComparison).hom ≫
        (Functor.associator _ _ _).inv := sorry

end UpperShriekCompChoice

/-- The middle functor in the compactification construction of the upper-shriek
compositor. -/
abbrev upperShriekCompMiddle
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (C : UpperShriekCompChoice f g) : Plus Z.obj.left ⥤ Plus X.obj.left :=
  C.A_g.plus ⋙ (C.A_bar.plus ⋙
    @OpenImmersion.pullbackPlus _ _ (ι C.P_bar)
      (instIsOpenImmersion _ _ C.P_bar))

/-- The displayed formula for the middle functor of the compositor. -/
theorem upperShriekCompMiddle_def
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (C : UpperShriekCompChoice f g) :
    upperShriekCompMiddle C =
      C.A_g.plus ⋙ (C.A_bar.plus ⋙
        @OpenImmersion.pullbackPlus _ _ (ι C.P_bar)
          (instIsOpenImmersion _ _ C.P_bar)) := sorry

/-- The proper-composition part of the upper-shriek compositor. -/
noncomputable def upperShriekProperComparison
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g) :
    upperShriek (f ≫ g) (comp f g C.P_g C.P_bar) C.A_fg.plus ≅
      upperShriekCompMiddle C :=
  Functor.isoWhiskerRight
      (PlusRightAdjoint.iso C.A_fg
        (PlusRightAdjoint.comp (ambientMorphism C.P_bar)
          (ambientMorphism C.P_g) C.A_bar C.A_g))
      (@OpenImmersion.pullbackPlus _ _ (ι C.P_bar)
        (instIsOpenImmersion _ _ C.P_bar)) ≪≫
    Functor.associator C.A_g.plus C.A_bar.plus
      (@OpenImmersion.pullbackPlus _ _ (ι C.P_bar)
        (instIsOpenImmersion _ _ C.P_bar))

/-- The forward map of the proper-composition part is the right-adjoint uniqueness map
followed by reassociation. -/
theorem upperShriekProperComparison_hom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g) :
    (upperShriekProperComparison f g C).hom =
      (Functor.isoWhiskerRight
        (PlusRightAdjoint.iso C.A_fg
          (PlusRightAdjoint.comp (ambientMorphism C.P_bar)
            (ambientMorphism C.P_g) C.A_bar C.A_g))
        (@OpenImmersion.pullbackPlus _ _ (ι C.P_bar)
          (instIsOpenImmersion _ _ C.P_bar))).hom ≫
      (Functor.associator C.A_g.plus C.A_bar.plus
        (@OpenImmersion.pullbackPlus _ _ (ι C.P_bar)
          (instIsOpenImmersion _ _ C.P_bar))).hom := sorry

/-- The open-base-change part of the upper-shriek compositor. -/
noncomputable def upperShriekOpenComparison
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (C : UpperShriekCompChoice f g) :
    upperShriekCompMiddle C ≅
      upperShriek g C.P_g C.A_g.plus ⋙ upperShriek f C.P_f C.A_f.plus :=
  Functor.isoWhiskerLeft C.A_g.plus C.openComparison ≪≫
    (Functor.associator C.A_g.plus
      (@OpenImmersion.pullbackPlus _ _ (ι C.P_g)
        (instIsOpenImmersion _ _ C.P_g))
      (upperShriek f C.P_f C.A_f.plus)).symm

/-- The forward map of the open part is the whiskered bounded open-base-change map
followed by reassociation. -/
theorem upperShriekOpenComparison_hom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (C : UpperShriekCompChoice f g) :
    (upperShriekOpenComparison C).hom =
      (Functor.isoWhiskerLeft C.A_g.plus C.openComparison).hom ≫
        (Functor.associator C.A_g.plus
          (@OpenImmersion.pullbackPlus _ _ (ι C.P_g)
            (instIsOpenImmersion _ _ C.P_g))
          (upperShriek f C.P_f C.A_f.plus)).inv := sorry

/-- A dense refinement of one complete compactification diagram by another. The maps
`map_f`, `map_g`, `map_bar`, and `map_fg` are the refinement maps. The displayed
upper-shriek isomorphisms are canonical mates whose compatibility follows from vertical
and horizontal composition of right mates. -/
structure UpperShriekCompRefinement
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C D : UpperShriekCompChoice f g) where
  /-- The refinement map for the compactification of `f`. -/
  map_f : C.P_f ⟶ D.P_f
  /-- The refinement map for the compactification of `g`. -/
  map_g : C.P_g ⟶ D.P_g
  /-- The refinement map between the intermediate compactifications. -/
  map_bar : ambient C.P_bar ⟶ ambient D.P_bar
  /-- The induced refinement map for the compactification of `f ≫ g`. -/
  map_fg : comp f g C.P_g C.P_bar ⟶ comp f g D.P_g D.P_bar
  /-- The intermediate refinement is compatible with the comparison maps `k`. -/
  map_k : ambientMap map_f ≫ D.k = C.k ≫ map_bar
  /-- The intermediate refinement lies over the refinement of the compactification of `g`. -/
  map_bar_over_g :
    map_bar ≫ ambientMorphism D.P_bar = ambientMorphism C.P_bar ≫ ambientMap map_g
  /-- The intermediate refinement restricts to the identity on the common open interior. -/
  map_bar_interior : ι C.P_bar ≫ map_bar = ι D.P_bar
  /-- The composite refinement has `map_bar` as its ambient map. -/
  map_fg_ambient : ambientMap map_fg = map_bar
  /-- The source compactification of `f` has dense interior. -/
  dense_f : IsDominant (ι C.P_f)
  /-- The source compactification of `g` has dense interior. -/
  dense_g : IsDominant (ι C.P_g)
  /-- The source intermediate compactification has dense interior. -/
  dense_bar : IsDominant (ι C.P_bar)
  /-- The source composite compactification has dense interior. -/
  dense_fg : IsDominant (ι (comp f g C.P_g C.P_bar))
  /-- The canonical upper-shriek comparison induced by `map_f`. -/
  upper_f :
    upperShriek f C.P_f C.A_f.plus ≅ upperShriek f D.P_f D.A_f.plus
  /-- The canonical upper-shriek comparison induced by `map_g`. -/
  upper_g :
    upperShriek g C.P_g C.A_g.plus ≅ upperShriek g D.P_g D.A_g.plus
  /-- The canonical upper-shriek comparison induced by `map_fg`. -/
  upper_fg :
    upperShriek (f ≫ g) (comp f g C.P_g C.P_bar) C.A_fg.plus ≅
      upperShriek (f ≫ g) (comp f g D.P_g D.P_bar) D.A_fg.plus
  /-- The comparison between the middle terms in the two compositor constructions. -/
  upper_middle :
    upperShriekCompMiddle C ≅ upperShriekCompMiddle D
  /-- Vertical mate composition, as in `DerivedBaseChange.mapOfRight_vcomp`, is compatible
  with the proper-composition part of the compositor. -/
  mapOfRight_vcomp :
    upper_fg ≪≫ upperShriekProperComparison f g D =
      upperShriekProperComparison f g C ≪≫ upper_middle
  /-- Horizontal mate composition, as in `DerivedBaseChange.mapOfRight_hcomp`, is
  compatible with the open-base-change part of the compositor. -/
  mapOfRight_hcomp :
    upper_middle ≪≫ upperShriekOpenComparison D =
      upperShriekOpenComparison C ≪≫
        Functor.isoWhiskerRight upper_g (upperShriek f C.P_f C.A_f.plus) ≪≫
        Functor.isoWhiskerLeft (upperShriek g D.P_g D.A_g.plus) upper_f

namespace UpperShriekCompRefinement

/-- Build a refinement of complete compactification diagrams from its geometric maps,
density properties, and their canonical upper-shriek mate comparisons. -/
def of
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    {C D : UpperShriekCompChoice f g}
    (map_f : C.P_f ⟶ D.P_f) (map_g : C.P_g ⟶ D.P_g)
    (map_bar : ambient C.P_bar ⟶ ambient D.P_bar)
    (map_fg : comp f g C.P_g C.P_bar ⟶ comp f g D.P_g D.P_bar)
    (map_k : ambientMap map_f ≫ D.k = C.k ≫ map_bar)
    (map_bar_over_g :
      map_bar ≫ ambientMorphism D.P_bar = ambientMorphism C.P_bar ≫ ambientMap map_g)
    (map_bar_interior : ι C.P_bar ≫ map_bar = ι D.P_bar)
    (map_fg_ambient : ambientMap map_fg = map_bar)
    (dense_f : IsDominant (ι C.P_f)) (dense_g : IsDominant (ι C.P_g))
    (dense_bar : IsDominant (ι C.P_bar))
    (dense_fg : IsDominant (ι (comp f g C.P_g C.P_bar)))
    (upper_f : upperShriek f C.P_f C.A_f.plus ≅ upperShriek f D.P_f D.A_f.plus)
    (upper_g : upperShriek g C.P_g C.A_g.plus ≅ upperShriek g D.P_g D.A_g.plus)
    (upper_fg :
      upperShriek (f ≫ g) (comp f g C.P_g C.P_bar) C.A_fg.plus ≅
        upperShriek (f ≫ g) (comp f g D.P_g D.P_bar) D.A_fg.plus)
    (upper_middle : upperShriekCompMiddle C ≅ upperShriekCompMiddle D)
    (mapOfRight_vcomp :
      upper_fg ≪≫ upperShriekProperComparison f g D =
        upperShriekProperComparison f g C ≪≫ upper_middle)
    (mapOfRight_hcomp :
      upper_middle ≪≫ upperShriekOpenComparison D =
        upperShriekOpenComparison C ≪≫
          Functor.isoWhiskerRight upper_g (upperShriek f C.P_f C.A_f.plus) ≪≫
          Functor.isoWhiskerLeft (upperShriek g D.P_g D.A_g.plus) upper_f) :
    UpperShriekCompRefinement f g C D where
  map_f := map_f
  map_g := map_g
  map_bar := map_bar
  map_fg := map_fg
  map_k := map_k
  map_bar_over_g := map_bar_over_g
  map_bar_interior := map_bar_interior
  map_fg_ambient := map_fg_ambient
  dense_f := dense_f
  dense_g := dense_g
  dense_bar := dense_bar
  dense_fg := dense_fg
  upper_f := upper_f
  upper_g := upper_g
  upper_fg := upper_fg
  upper_middle := upper_middle
  mapOfRight_vcomp := mapOfRight_vcomp
  mapOfRight_hcomp := mapOfRight_hcomp

end UpperShriekCompRefinement

/-- A common dense refinement of two complete compactification diagrams. -/
structure UpperShriekCompCommonRefinement
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C D : UpperShriekCompChoice f g) where
  /-- The complete compactification diagram refining both inputs. -/
  choice : UpperShriekCompChoice f g
  /-- Its refinement map to the first input. -/
  left : UpperShriekCompRefinement f g choice C
  /-- Its refinement map to the second input. -/
  right : UpperShriekCompRefinement f g choice D

namespace UpperShriekCompCommonRefinement

/-- Package a complete compactification diagram and its two dense refinement diagrams. -/
def of
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    {C D : UpperShriekCompChoice f g} (choice : UpperShriekCompChoice f g)
    (left : UpperShriekCompRefinement f g choice C)
    (right : UpperShriekCompRefinement f g choice D) :
    UpperShriekCompCommonRefinement f g C D where
  choice := choice
  left := left
  right := right

end UpperShriekCompCommonRefinement

/-- Any two complete compactification diagrams admit a common dense refinement diagram. -/
theorem exists_upperShriekCompCommonRefinement
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C D : UpperShriekCompChoice f g) :
    Nonempty (UpperShriekCompCommonRefinement f g C D) := sorry

/-- The compositor is natural for a dense refinement diagram. Its proper-composition
and open-base-change pieces are compatible by vertical and horizontal composition of
right mates. -/
theorem upperShriekCompIso_natural_of_refinement
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C D : UpperShriekCompChoice f g)
    (R : UpperShriekCompRefinement f g C D) :
    R.upper_fg ≪≫ D.compIso f g =
      C.compIso f g ≪≫
        Functor.isoWhiskerRight R.upper_g
          (upperShriek f C.P_f C.A_f.plus) ≪≫
        Functor.isoWhiskerLeft (upperShriek g D.P_g D.A_g.plus)
          R.upper_f := sorry

/-- The canonical compositor is independent of two complete compatible choices: after
passing through any common dense refinement, the comparison square for `(f ≫ g) !`,
`g !`, and `f !` commutes. -/
theorem upperShriekCompIso_independent
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C D : UpperShriekCompChoice f g)
    (R : UpperShriekCompCommonRefinement f g C D) :
    ((UpperShriekCompRefinement.upper_fg R.left).symm ≪≫
        UpperShriekCompRefinement.upper_fg R.right) ≪≫ D.compIso f g =
      C.compIso f g ≪≫
        Functor.isoWhiskerRight
          ((UpperShriekCompRefinement.upper_g R.left).symm ≪≫
            UpperShriekCompRefinement.upper_g R.right)
          (upperShriek f C.P_f C.A_f.plus) ≪≫
        Functor.isoWhiskerLeft (upperShriek g D.P_g D.A_g.plus)
          ((UpperShriekCompRefinement.upper_f R.left).symm ≪≫
            UpperShriekCompRefinement.upper_f R.right) := sorry

end Scheme.Compactification.Of
end AlgebraicGeometry
