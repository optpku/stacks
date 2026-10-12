/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap81.Lemma_81_6_2_Pushout
public import stacks_project.Chap81.Lemma_81_6_6_Flat

/-!
# Glueing relatively flat quasi-coherent modules along a pushout

A thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` of algebraic
spaces determine a pushout `Y ⨿_X X'`. Relatively flat quasi-coherent modules
on a test space over the pushout are equivalent to compatible pairs of
relatively flat quasi-coherent modules on the two base changes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FlatQCoh.Pushout

variable {S : Scheme.{u}} {X X' Y V' : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
  [IsThickening i] [Affine f] (p : V' ⟶ pushout i f)

/-- The two legs defining the canonical map from `U` to `V` agree over the pushout. -/
theorem leftMap_condition :
    pullback.fst p (i ≫ pushout.inl i f) ≫ p =
      (pullback.snd p (i ≫ pushout.inl i f) ≫ f) ≫ pushout.inr i f := sorry

/-- The canonical morphism `U ⟶ V` between the two chosen base changes. -/
def leftMap : pullback p (i ≫ pushout.inl i f) ⟶ pullback p (pushout.inr i f) :=
  pullback.lift (pullback.fst p (i ≫ pushout.inl i f))
    (pullback.snd p (i ≫ pushout.inl i f) ≫ f) (leftMap_condition i f p)

/-- The composite of `leftMap` with the projection to `V'` is the projection from `U`. -/
theorem leftMap_fst :
    leftMap i f p ≫ pullback.fst p (pushout.inr i f) =
      pullback.fst p (i ≫ pushout.inl i f) := sorry

/-- The composite of `leftMap` with the projection to `Y` is the projection to `X` followed
by `f`. -/
theorem leftMap_snd :
    leftMap i f p ≫ pullback.snd p (pushout.inr i f) =
      pullback.snd p (i ≫ pushout.inl i f) ≫ f := sorry

/-- The two legs defining the canonical map from `U` to `U'` agree over the pushout. -/
theorem rightMap_condition :
    pullback.fst p (i ≫ pushout.inl i f) ≫ p =
      (pullback.snd p (i ≫ pushout.inl i f) ≫ i) ≫ pushout.inl i f := sorry

/-- The canonical morphism `U ⟶ U'` between the two chosen base changes. -/
def rightMap : pullback p (i ≫ pushout.inl i f) ⟶ pullback p (pushout.inl i f) :=
  pullback.lift (pullback.fst p (i ≫ pushout.inl i f))
    (pullback.snd p (i ≫ pushout.inl i f) ≫ i) (rightMap_condition i f p)

/-- The composite of `rightMap` with the projection to `V'` is the projection from `U`. -/
theorem rightMap_fst :
    rightMap i f p ≫ pullback.fst p (pushout.inl i f) =
      pullback.fst p (i ≫ pushout.inl i f) := sorry

/-- The composite of `rightMap` with the projection to `X'` is the projection to `X` followed
by `i`. -/
theorem rightMap_snd :
    rightMap i f p ≫ pullback.snd p (pushout.inl i f) =
      pullback.snd p (i ≫ pushout.inl i f) ≫ i := sorry

/-- Restriction of relatively flat quasi-coherent modules on `V` to modules on `U`. -/
def leftOverlap :
    FlatQCoh (pullback.snd p (pushout.inr i f)) ⥤
      (pullback p (i ≫ pushout.inl i f)).Modules :=
  inclusion (pullback.snd p (pushout.inr i f)) ⋙ QCoh.pullback (leftMap i f p) ⋙
    QCoh.inclusion (pullback p (i ≫ pushout.inl i f))

/-- The underlying object of `leftOverlap` is pullback along `leftMap`. -/
theorem leftOverlap_obj (G : FlatQCoh (pullback.snd p (pushout.inr i f))) :
    (leftOverlap i f p).obj G = (Modules.pullback (leftMap i f p)).obj G.obj.obj := sorry

/-- Restriction of relatively flat quasi-coherent modules on `U'` to modules on `U`. -/
def rightOverlap :
    FlatQCoh (pullback.snd p (pushout.inl i f)) ⥤
      (pullback p (i ≫ pushout.inl i f)).Modules :=
  inclusion (pullback.snd p (pushout.inl i f)) ⋙ QCoh.pullback (rightMap i f p) ⋙
    QCoh.inclusion (pullback p (i ≫ pushout.inl i f))

/-- The underlying object of `rightOverlap` is pullback along `rightMap`. -/
theorem rightOverlap_obj (F' : FlatQCoh (pullback.snd p (pushout.inl i f))) :
    (rightOverlap i f p).obj F' =
      (Modules.pullback (rightMap i f p)).obj F'.obj.obj := sorry

/-- Compatible relatively flat quasi-coherent modules on `V` and `U'`, identified on `U`. -/
abbrev Gluing := CategoricalPullback (leftOverlap i f p) (rightOverlap i f p)

/-- The canonical comparison between the two iterated pullbacks of a module on `V'` to `U`. -/
def comparison (G' : FlatQCoh p) :
    (leftOverlap i f p).obj ((baseChange p (pushout.inr i f)).obj G') ≅
      (rightOverlap i f p).obj ((baseChange p (pushout.inl i f)).obj G') :=
  (Modules.pullbackComp (leftMap i f p) (pullback.fst p (pushout.inr i f))).app
      G'.obj.obj ≪≫
    (eqToIso (congrArg Modules.pullback (pullback.lift_fst _ _ _))).app G'.obj.obj ≪≫
    ((eqToIso (congrArg Modules.pullback (pullback.lift_fst _ _ _))).app G'.obj.obj).symm ≪≫
    ((Modules.pullbackComp (rightMap i f p) (pullback.fst p (pushout.inl i f))).app
      G'.obj.obj).symm

/-- The canonical comparison is natural in the relatively flat quasi-coherent module. -/
theorem comparison_naturality {G' H' : FlatQCoh p} (a : G' ⟶ H') :
    (baseChange p (pushout.inr i f) ⋙ leftOverlap i f p).map a ≫
        (comparison i f p H').hom =
      (comparison i f p G').hom ≫
        (baseChange p (pushout.inl i f) ⋙ rightOverlap i f p).map a := sorry

/-- The canonical comparisons assemble into a natural isomorphism of overlap functors. -/
def comparisonNatIso :
    baseChange p (pushout.inr i f) ⋙ leftOverlap i f p ≅
      baseChange p (pushout.inl i f) ⋙ rightOverlap i f p :=
  NatIso.ofComponents (comparison i f p) (fun a ↦ comparison_naturality i f p a)

/-- The component of `comparisonNatIso` is the canonical comparison isomorphism. -/
theorem comparisonNatIso_app (G' : FlatQCoh p) :
    (comparisonNatIso i f p).app G' = comparison i f p G' := sorry

/-- The canonical functor sending a module on `V'` to its restrictions on `V` and `U'`, with
their canonical identification on `U`. -/
def gluingFunctor : FlatQCoh p ⥤ Gluing i f p :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (leftOverlap i f p) (rightOverlap i f p) (FlatQCoh p)).obj
      { fst := baseChange p (pushout.inr i f)
        snd := baseChange p (pushout.inl i f)
        iso := comparisonNatIso i f p }

/-- The first component of the canonical gluing functor is base change to `V`. -/
theorem gluingFunctor_obj_fst (G' : FlatQCoh p) :
    ((gluingFunctor i f p).obj G').fst =
      (baseChange p (pushout.inr i f)).obj G' := sorry

/-- The second component of the canonical gluing functor is base change to `U'`. -/
theorem gluingFunctor_obj_snd (G' : FlatQCoh p) :
    ((gluingFunctor i f p).obj G').snd =
      (baseChange p (pushout.inl i f)).obj G' := sorry

/-- The structural isomorphism of the canonical gluing functor is `comparison`. -/
theorem gluingFunctor_obj_iso (G' : FlatQCoh p) :
    ((gluingFunctor i f p).obj G').iso = comparison i f p G' := sorry

/-- Pullback from `V'` is an equivalence onto compatible relatively flat quasi-coherent
modules on `V` and `U'`. -/
instance gluingFunctorIsEquivalence : Functor.IsEquivalence (gluingFunctor i f p) := sorry

/-- A relatively flat quasi-coherent module on `V'` is of finite type exactly when both
components of its canonical gluing datum are of finite type. -/
theorem finiteType_iff (G' : FlatQCoh p) :
    IsFiniteType G'.obj.obj ↔
      IsFiniteType ((gluingFunctor i f p).obj G').fst.obj.obj ∧
        IsFiniteType ((gluingFunctor i f p).obj G').snd.obj.obj := sorry

/-- If `p` is locally of finite presentation, a relatively flat quasi-coherent module on
`V'` is finitely presented exactly when both components of its canonical gluing datum are. -/
theorem finitePresentation_iff [LocallyOfFinitePresentation p] (G' : FlatQCoh p) :
    IsFinitePresentation G'.obj.obj ↔
      IsFinitePresentation ((gluingFunctor i f p).obj G').fst.obj.obj ∧
        IsFinitePresentation ((gluingFunctor i f p).obj G').snd.obj.obj := sorry

end AlgebraicGeometry.AlgebraicSpace.FlatQCoh.Pushout
