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
    IsProper (P_bar.obj.right.hom ≫ P_g.obj.right.hom) := by
  letI : IsProper P_bar.obj.right.hom := P_bar.property.isProper
  letI : IsProper P_g.obj.right.hom := P_g.property.isProper
  infer_instance

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

/-- Expose properness of the composite compactification's ambient morphism to instance
search, hence also its quasi-compactness and quasi-separatedness. -/
instance instCompAmbientIsProper
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P_g : Of Z.obj.left (Over.mk g.hom.left))
    (P_bar : Of P_g.obj.right.left (Over.mk (f.hom.left ≫ ι P_g))) :
    IsProper (ambientMorphism (comp f g P_g P_bar)) :=
  compAmbient_isProper f g P_g P_bar

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

/-- The counit comparison `Rq_* a_P → a_Q` attached to an actual morphism `q` of
compactifications. It is the transpose, under the adjunction for `Q`, of the counit
for `P`, using the canonical pushforward-composition comparison. -/
noncomputable def upperShriekRefinementPushforward
    {T : Scheme.{u}} [IsNoetherian T] {U : Over T} {P Q : Of T U}
    (q : P ⟶ Q) (A : PlusRightAdjoint (ambientMorphism P))
    (B : PlusRightAdjoint (ambientMorphism Q)) (K : DerivedQCoh T) :
    (pushforwardCohomologyIn (ambientMap q)).obj (A.right.obj K) ⟶ B.right.obj K :=
  let pushforwardComp :=
    pushforwardCompIso (ambientMap q) (ambientMorphism Q)
        (RingedSpace.modulePullbackDerived.compComparison_isIso
          (ambientMap q).toShHom (ambientMorphism Q).toShHom) ≪≫
      eqToIso (congrArg (fun r : ambient P ⟶ T ↦ pushforwardCohomologyIn r)
        (Over.w q.hom.right))
  B.adjunction.homEquiv _ K
    (pushforwardComp.hom.app (A.right.obj K) ≫ A.adjunction.counit.app K)

/-- Ordinary base change for the square with identity on the common interior. The
formula uses only pullback composition and the counit for `q^* ⊣ Rq_*`; no inverse
of an unproved base-change isomorphism is used. For a dense source this map is
invertible, by the interior-preimage assertion of Stacks 0ATU. -/
noncomputable def upperShriekRefinementRestriction
    {T : Scheme.{u}} [IsNoetherian T] {U : Over T} {P Q : Of T U}
    (q : P ⟶ Q) (K : DerivedQCoh (ambient P)) :
    (pullback (ι Q)).obj ((pushforwardCohomologyIn (ambientMap q)).obj K) ⟶
      (pullback (ι P)).obj K :=
  (UpperShriekCompChoice.pullbackCompIsoOfEq (ι P) (ambientMap q) (ι Q)
      (ι_comp_ambientMap q)).inv.app ((pushforwardCohomologyIn (ambientMap q)).obj K) ≫
    (pullback (ι P)).map ((pullbackPushforwardAdjunction (ambientMap q)).counit.app K)

/-- Express a bounded comparison in the ambient derived category, using the specified
compatibilities of its two right-adjoint models. -/
noncomputable def upperShriekRefinementAmbientApp
    {T : Scheme.{u}} [IsNoetherian T] {U : Over T} {P Q : Of T U}
    (A : PlusRightAdjoint (ambientMorphism P))
    (B : PlusRightAdjoint (ambientMorphism Q))
    (η : A.plus ⋙ OpenImmersion.pullbackPlus (ι P) ⟶
      B.plus ⋙ OpenImmersion.pullbackPlus (ι Q)) (K : Plus T) :
    (inclusion U.left).obj ((pullback (ι P)).obj
        (A.right.obj ((DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty T.toRingedSpace)).obj K))) ⟶
      (inclusion U.left).obj ((pullback (ι Q)).obj
        (B.right.obj ((DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty T.toRingedSpace)).obj K))) :=
  (A.openRestrictionAmbientIso (ι P)).inv.app K ≫
    (DerivedCategory.Plus.CohomologyIn.ambient
      (RingedSpace.quasiCoherentModuleProperty U.left.toRingedSpace)).map (η.app K) ≫
    (B.openRestrictionAmbientIso (ι Q)).hom.app K

/-- The mate specification for the comparison `α_q` of Stacks 0AA0.

After ordinary base change along the common interior, the comparison must equal
the restriction of the actual counit transpose for `q`. For a dense source the
ordinary base-change map is invertible, so this equation uniquely determines `η`.
This specification retains bounded comparison data without extracting inverses
from an unproved invertibility theorem. -/
def IsUpperShriekRefinementMap
    {T : Scheme.{u}} [IsNoetherian T] {U : Over T} {P Q : Of T U}
    (q : P ⟶ Q) (A : PlusRightAdjoint (ambientMorphism P))
    (B : PlusRightAdjoint (ambientMorphism Q))
    (η : A.plus ⋙ OpenImmersion.pullbackPlus (ι P) ⟶
      B.plus ⋙ OpenImmersion.pullbackPlus (ι Q)) : Prop :=
  ∀ K : Plus T,
    let K₀ := (DerivedCategory.Plus.CohomologyIn.toUnbounded
      (RingedSpace.quasiCoherentModuleProperty T.toRingedSpace)).obj K
    (inclusion U.left).map (upperShriekRefinementRestriction q (A.right.obj K₀)) ≫
        upperShriekRefinementAmbientApp A B η K =
      (inclusion U.left).map ((pullback (ι Q)).map
        (upperShriekRefinementPushforward q A B K₀))

/-- The geometric mate specification has at most one solution for a dense source. -/
theorem IsUpperShriekRefinementMap.hom_ext
    {T : Scheme.{u}} [IsNoetherian T] {U : Over T} {P Q : Of T U}
    (q : P ⟶ Q) (dense : IsDominant (ι P))
    (A : PlusRightAdjoint (ambientMorphism P))
    (B : PlusRightAdjoint (ambientMorphism Q))
    {η θ : A.plus ⋙ OpenImmersion.pullbackPlus (ι P) ⟶
      B.plus ⋙ OpenImmersion.pullbackPlus (ι Q)}
    (hη : IsUpperShriekRefinementMap q A B η)
    (hθ : IsUpperShriekRefinementMap q A B θ) : η = θ := sorry

/-- Identity geometry has the identity mate. -/
theorem isUpperShriekRefinementMap_id
    {T : Scheme.{u}} [IsNoetherian T] {U : Over T} (P : Of T U)
    (A : PlusRightAdjoint (ambientMorphism P)) :
    IsUpperShriekRefinementMap (𝟙 P) A A (𝟙 _) := sorry

/-- Two invertible realizations of the same geometric mate agree. -/
theorem IsUpperShriekRefinementMap.iso_ext
    {T : Scheme.{u}} [IsNoetherian T] {U : Over T} {P Q : Of T U}
    (q : P ⟶ Q) (dense : IsDominant (ι P))
    (A : PlusRightAdjoint (ambientMorphism P))
    (B : PlusRightAdjoint (ambientMorphism Q))
    {e e' : A.plus ⋙ OpenImmersion.pullbackPlus (ι P) ≅
      B.plus ⋙ OpenImmersion.pullbackPlus (ι Q)}
    (he : IsUpperShriekRefinementMap q A B e.hom)
    (he' : IsUpperShriekRefinementMap q A B e'.hom) : e = e' :=
  Iso.ext (IsUpperShriekRefinementMap.hom_ext q dense A B he he')

/-- An invertible comparison over identity geometry is forced to be the identity. -/
theorem IsUpperShriekRefinementMap.iso_id
    {T : Scheme.{u}} [IsNoetherian T] {U : Over T} (P : Of T U)
    (dense : IsDominant (ι P)) (A : PlusRightAdjoint (ambientMorphism P))
    {e : A.plus ⋙ OpenImmersion.pullbackPlus (ι P) ≅
      A.plus ⋙ OpenImmersion.pullbackPlus (ι P)}
    (he : IsUpperShriekRefinementMap (𝟙 P) A A e.hom) : e = Iso.refl _ :=
  IsUpperShriekRefinementMap.iso_ext (𝟙 P) dense A A he
    (isUpperShriekRefinementMap_id P A)

/-- Mate comparisons compose along the actual composite of geometric refinements. -/
theorem IsUpperShriekRefinementMap.comp
    {T : Scheme.{u}} [IsNoetherian T] {U : Over T} {P Q R : Of T U}
    {q : P ⟶ Q} {r : Q ⟶ R}
    {A : PlusRightAdjoint (ambientMorphism P)}
    {B : PlusRightAdjoint (ambientMorphism Q)}
    {C : PlusRightAdjoint (ambientMorphism R)}
    {η : A.plus ⋙ OpenImmersion.pullbackPlus (ι P) ⟶
      B.plus ⋙ OpenImmersion.pullbackPlus (ι Q)}
    {θ : B.plus ⋙ OpenImmersion.pullbackPlus (ι Q) ⟶
      C.plus ⋙ OpenImmersion.pullbackPlus (ι R)}
    (hη : IsUpperShriekRefinementMap q A B η)
    (hθ : IsUpperShriekRefinementMap r B C θ) :
    IsUpperShriekRefinementMap (q ≫ r) A C (η ≫ θ) := sorry

/-- Existence is kept in `Prop`: this theorem is not used to choose comparison data. -/
theorem exists_upperShriekRefinementIso
    {T : Scheme.{u}} [IsNoetherian T] {U : Over T} {P Q : Of T U}
    (q : P ⟶ Q) (dense : IsDominant (ι P))
    (A : PlusRightAdjoint (ambientMorphism P))
    (B : PlusRightAdjoint (ambientMorphism Q)) :
    ∃ e : A.plus ⋙ OpenImmersion.pullbackPlus (ι P) ≅
      B.plus ⋙ OpenImmersion.pullbackPlus (ι Q),
      IsUpperShriekRefinementMap q A B e.hom := sorry

/-- A comparison system realizes Stacks 0AA0 when each of its maps has the actual
geometric counit/base-change specification. Functoriality alone does not imply this. -/
def UpperShriekComparisonSystem.IsCanonical
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} {f : X ⟶ Y}
    (H : UpperShriekComparisonSystem f) : Prop :=
  ∀ {P Q : Of Y.obj.left (Over.mk f.hom.left)} (q : P ⟶ Q),
    IsDominant (ι P) → IsUpperShriekRefinementMap q (H.model P) (H.model Q)
      ((H.modelIso P).inv ≫ H.comparison.map q ≫ (H.modelIso Q).hom)

/-- The comparison supplied by a canonical 0AA0 system agrees with every realization
of the geometric mate. This bridge requires canonicality of the system's maps. -/
theorem UpperShriekComparisonSystem.iso_eq_of_refinement
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} {f : X ⟶ Y}
    (H : UpperShriekComparisonSystem f) (hH : H.IsCanonical)
    {P Q : Of Y.obj.left (Over.mk f.hom.left)} (q : P ⟶ Q)
    (dense : IsDominant (ι P))
    (e : upperShriek f P (H.model P).plus ≅ upperShriek f Q (H.model Q).plus)
    (he : IsUpperShriekRefinementMap q (H.model P) (H.model Q) e.hom) :
    H.iso P Q (H.model P) (H.model Q) = e := sorry

/-- The composite proper right-adjoint model used in the middle term. -/
noncomputable def UpperShriekCompChoice.compositeModel
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (C : UpperShriekCompChoice f g) :
    PlusRightAdjoint (ambientMorphism (comp f g C.P_g C.P_bar)) :=
  PlusRightAdjoint.comp (ambientMorphism C.P_bar) (ambientMorphism C.P_g) C.A_bar C.A_g

/-- Reassociate the restriction of the composite proper model to the middle term. -/
noncomputable def UpperShriekCompChoice.middleReassoc
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (C : UpperShriekCompChoice f g) :
    upperShriek (f ≫ g) (comp f g C.P_g C.P_bar) C.compositeModel.plus ≅
      upperShriekCompMiddle C :=
  Functor.associator _ _ _

/-- Geometric data of a dense refinement of complete compactification diagrams.
No functor comparison or compositor-compatibility conclusion is part of this layer. -/
structure UpperShriekCompGeometry
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

/-- A geometric refinement with specified realizations of its canonical mates.
Each comparison is anchored by the counit/base-change specification for its
actual geometric map. The middle comparison uses `map_bar`, through
`map_fg_ambient`, and the composed proper adjunctions. Compatibility with the
compositor is a theorem, not constructor input. -/
structure UpperShriekCompRefinement
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C D : UpperShriekCompChoice f g) extends UpperShriekCompGeometry f g C D where
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
  /-- The `f` comparison is the mate for the actual `map_f`. -/
  upper_f_spec : IsUpperShriekRefinementMap map_f C.A_f D.A_f upper_f.hom
  /-- The `g` comparison is the mate for the actual `map_g`. -/
  upper_g_spec : IsUpperShriekRefinementMap map_g C.A_g D.A_g upper_g.hom
  /-- The composite comparison is the mate for the actual `map_fg`. -/
  upper_fg_spec : IsUpperShriekRefinementMap map_fg C.A_fg D.A_fg upper_fg.hom
  /-- The middle comparison is the mate for the same ambient refinement, with the
  right adjoints composed before restriction. -/
  upper_middle_spec :
    IsUpperShriekRefinementMap map_fg C.compositeModel D.compositeModel
      (C.middleReassoc ≪≫ upper_middle ≪≫ D.middleReassoc.symm).hom

namespace UpperShriekCompRefinement

/-- Reassociation transports the identity mate to the middle term. -/
theorem middle_refl_spec
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (C : UpperShriekCompChoice f g) :
    IsUpperShriekRefinementMap (𝟙 (comp f g C.P_g C.P_bar))
      C.compositeModel C.compositeModel
      (C.middleReassoc ≪≫ Iso.refl _ ≪≫ C.middleReassoc.symm).hom := sorry

/-- Reassociation transports the composite of two middle mates to the outer mate. -/
theorem middle_trans_spec
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    {C D E : UpperShriekCompChoice f g}
    (R : UpperShriekCompRefinement f g C D)
    (R' : UpperShriekCompRefinement f g D E) :
    IsUpperShriekRefinementMap (R.map_fg ≫ R'.map_fg)
      C.compositeModel E.compositeModel
      (C.middleReassoc ≪≫ (R.upper_middle ≪≫ R'.upper_middle) ≪≫
        E.middleReassoc.symm).hom := sorry

/-- Identity geometric refinement, with identity comparison data. Only the density
properties of the source are needed; all mate-specification obligations are proofs. -/
def refl
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (C : UpperShriekCompChoice f g)
    (dense_f : IsDominant (ι C.P_f)) (dense_g : IsDominant (ι C.P_g))
    (dense_bar : IsDominant (ι C.P_bar))
    (dense_fg : IsDominant (ι (comp f g C.P_g C.P_bar))) :
    UpperShriekCompRefinement f g C C where
  map_f := 𝟙 _
  map_g := 𝟙 _
  map_bar := 𝟙 _
  map_fg := 𝟙 _
  map_k := by
    change 𝟙 _ ≫ C.k = C.k ≫ 𝟙 _
    simp
  map_bar_over_g := by
    change 𝟙 _ ≫ ambientMorphism C.P_bar = ambientMorphism C.P_bar ≫ 𝟙 _
    simp
  map_bar_interior := by simp
  map_fg_ambient := rfl
  dense_f := dense_f
  dense_g := dense_g
  dense_bar := dense_bar
  dense_fg := dense_fg
  upper_f := Iso.refl _
  upper_g := Iso.refl _
  upper_fg := Iso.refl _
  upper_middle := Iso.refl _
  upper_f_spec := isUpperShriekRefinementMap_id C.P_f C.A_f
  upper_g_spec := isUpperShriekRefinementMap_id C.P_g C.A_g
  upper_fg_spec := isUpperShriekRefinementMap_id _ C.A_fg
  upper_middle_spec := middle_refl_spec C

/-- Compose geometric refinements and their specified mates. The comparison data
are the actual composites, and their specifications follow by mate composition. -/
def trans
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    {C D E : UpperShriekCompChoice f g}
    (R : UpperShriekCompRefinement f g C D)
    (R' : UpperShriekCompRefinement f g D E) :
    UpperShriekCompRefinement f g C E where
  map_f := R.map_f ≫ R'.map_f
  map_g := R.map_g ≫ R'.map_g
  map_bar := R.map_bar ≫ R'.map_bar
  map_fg := R.map_fg ≫ R'.map_fg
  map_k := by
    change (ambientMap R.map_f ≫ ambientMap R'.map_f) ≫ E.k =
      C.k ≫ (R.map_bar ≫ R'.map_bar)
    rw [Category.assoc, R'.map_k, ← Category.assoc, R.map_k, Category.assoc]
  map_bar_over_g := by
    change (R.map_bar ≫ R'.map_bar) ≫ ambientMorphism E.P_bar =
      ambientMorphism C.P_bar ≫ (ambientMap R.map_g ≫ ambientMap R'.map_g)
    rw [Category.assoc, R'.map_bar_over_g, ← Category.assoc, R.map_bar_over_g,
      Category.assoc]
  map_bar_interior := by
    rw [← Category.assoc, R.map_bar_interior]
    exact R'.map_bar_interior
  map_fg_ambient := by
    change ambientMap R.map_fg ≫ ambientMap R'.map_fg = R.map_bar ≫ R'.map_bar
    rw [R.map_fg_ambient, R'.map_fg_ambient]
    rfl
  dense_f := R.dense_f
  dense_g := R.dense_g
  dense_bar := R.dense_bar
  dense_fg := R.dense_fg
  upper_f := R.upper_f ≪≫ R'.upper_f
  upper_g := R.upper_g ≪≫ R'.upper_g
  upper_fg := R.upper_fg ≪≫ R'.upper_fg
  upper_middle := R.upper_middle ≪≫ R'.upper_middle
  upper_f_spec := R.upper_f_spec.comp R'.upper_f_spec
  upper_g_spec := R.upper_g_spec.comp R'.upper_g_spec
  upper_fg_spec := R.upper_fg_spec.comp R'.upper_fg_spec
  upper_middle_spec := middle_trans_spec R R'

/-- Associativity of refinement composition includes the cocycle law for all four
canonical comparison isomorphisms. -/
theorem trans_assoc
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    {C D E F : UpperShriekCompChoice f g}
    (R : UpperShriekCompRefinement f g C D)
    (R' : UpperShriekCompRefinement f g D E)
    (R'' : UpperShriekCompRefinement f g E F) :
    (R.trans R').trans R'' = R.trans (R'.trans R'') := sorry

/-- Build a refinement from geometry and comparisons satisfying the actual mate
specifications. Neither compositor-compatibility equation is required. -/
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
    (upper_f_spec : IsUpperShriekRefinementMap map_f C.A_f D.A_f upper_f.hom)
    (upper_g_spec : IsUpperShriekRefinementMap map_g C.A_g D.A_g upper_g.hom)
    (upper_fg_spec : IsUpperShriekRefinementMap map_fg C.A_fg D.A_fg upper_fg.hom)
    (upper_middle_spec :
      IsUpperShriekRefinementMap map_fg C.compositeModel D.compositeModel
        (C.middleReassoc ≪≫ upper_middle ≪≫ D.middleReassoc.symm).hom) :
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
  upper_f_spec := upper_f_spec
  upper_g_spec := upper_g_spec
  upper_fg_spec := upper_fg_spec
  upper_middle_spec := upper_middle_spec

/-- Vertical composition of the actual mates is compatible with proper composition
(Stacks 0ATQ), using right-adjoint uniqueness for the composed proper maps. -/
theorem mapOfRight_vcomp
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    {C D : UpperShriekCompChoice f g} (R : UpperShriekCompRefinement f g C D) :
    R.upper_fg ≪≫ upperShriekProperComparison f g D =
      upperShriekProperComparison f g C ≪≫ R.upper_middle := sorry

/-- Pasting the actual open-base-change mates around the intermediate geometric
square gives the same outer mate (Stacks 0ATQ and 0ATR). -/
theorem mapOfRight_hcomp
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    {C D : UpperShriekCompChoice f g} (R : UpperShriekCompRefinement f g C D) :
    R.upper_middle ≪≫ upperShriekOpenComparison D =
      upperShriekOpenComparison C ≪≫
        Functor.isoWhiskerRight R.upper_g (upperShriek f C.P_f C.A_f.plus) ≪≫
        Functor.isoWhiskerLeft (upperShriek g D.P_g D.A_g.plus) R.upper_f := sorry

end UpperShriekCompRefinement

/-- The geometric common-refinement assertion of Stacks 0ATU, before adding any
right-adjoint mate realizations. -/
theorem exists_upperShriekCompCommonGeometry
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C D : UpperShriekCompChoice f g) :
    ∃ E : UpperShriekCompChoice f g,
      Nonempty (UpperShriekCompGeometry f g E C) ∧
        Nonempty (UpperShriekCompGeometry f g E D) := sorry

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

/-- The three 0AA0 comparison isomorphisms obtained from a common refinement are
independent of that common refinement, by cofilteredness and the mate cocycle law. -/
theorem comparisons_independent
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} {f : X ⟶ Y} {g : Y ⟶ Z}
    {C D : UpperShriekCompChoice f g}
    (R R' : UpperShriekCompCommonRefinement f g C D) :
    R.left.upper_f.symm ≪≫ R.right.upper_f =
        R'.left.upper_f.symm ≪≫ R'.right.upper_f ∧
      R.left.upper_g.symm ≪≫ R.right.upper_g =
        R'.left.upper_g.symm ≪≫ R'.right.upper_g ∧
      R.left.upper_fg.symm ≪≫ R.right.upper_fg =
        R'.left.upper_fg.symm ≪≫ R'.right.upper_fg := sorry

end UpperShriekCompCommonRefinement

/-- Any two complete diagrams admit a common geometric refinement and realizations
of its canonical mates. Only existence is asserted; no data is chosen from it. -/
theorem exists_upperShriekCompCommonRefinement
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C D : UpperShriekCompChoice f g) :
    Nonempty (UpperShriekCompCommonRefinement f g C D) := sorry

/-- The displayed proper and open comparisons are the two factors of the compositor. -/
theorem upperShriekCompIso_factorization
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g) :
    C.compIso f g = upperShriekProperComparison f g C ≪≫
      upperShriekOpenComparison C := by
  apply Iso.ext
  simp [UpperShriekCompChoice.compIso, upperShriekProperComparison,
    upperShriekOpenComparison]
  rfl

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
          R.upper_f := by
  rw [upperShriekCompIso_factorization f g C, upperShriekCompIso_factorization f g D]
  calc
    R.upper_fg ≪≫ (upperShriekProperComparison f g D ≪≫
        upperShriekOpenComparison D) =
        (R.upper_fg ≪≫ upperShriekProperComparison f g D) ≪≫
          upperShriekOpenComparison D := by simp only [Iso.trans_assoc]
    _ = (upperShriekProperComparison f g C ≪≫ R.upper_middle) ≪≫
          upperShriekOpenComparison D := by rw [R.mapOfRight_vcomp]
    _ = upperShriekProperComparison f g C ≪≫
          (R.upper_middle ≪≫ upperShriekOpenComparison D) := by
            simp only [Iso.trans_assoc]
    _ = upperShriekProperComparison f g C ≪≫
          (upperShriekOpenComparison C ≪≫
            Functor.isoWhiskerRight R.upper_g (upperShriek f C.P_f C.A_f.plus) ≪≫
            Functor.isoWhiskerLeft (upperShriek g D.P_g D.A_g.plus) R.upper_f) := by
              rw [R.mapOfRight_hcomp]
    _ = _ := by simp only [Iso.trans_assoc]

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
