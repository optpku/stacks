/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.IsoClasses
import ReasLib.CategoryTheory.Fibered.Setoids.Equivalence
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.GroupoidTarget

/-!
# Representing 2-fibre products by morphisms of algebraic spaces

A 2-fibre product of categories fibred in groupoids over `(Sch/S)_fppf` may be
compared with a morphism of algebraic spaces representing the apex and the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A morphism `f' : F ⟶ G` of algebraic spaces over `S` represents the first
projection of the 2-fibre product of `g : Z ⟶ Y` with `f : X ⟶ Y` when `G`
represents `Z`, `F` represents the apex, and the induced 1-morphism of groupoid
fibrations is 2-isomorphic to `TwoFibreProduct.fst g f`. -/
def RepresentsTwoFibreProductOnSpace {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
    (F G : AlgebraicSpace S) (f' : F ⟶ G) : Prop :=
  ∃ (eZ : Z ≌ G.toGroupoids)
    (eApex : TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids),
    Nonempty
      (eApex.hom ≫ toGroupoids.map f' ≅
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f ≫ eZ.hom)

/-- Representing a 2-fibre product on spaces is equivalent to the existence of
representing equivalences whose projection triangle identifies `toGroupoids.map f'`
with `TwoFibreProduct.fst`. -/
theorem RepresentsTwoFibreProductOnSpace.iff {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {F G : AlgebraicSpace S} {f' : F ⟶ G} :
    RepresentsTwoFibreProductOnSpace f g F G f' ↔
      ∃ (eZ : Z ≌ G.toGroupoids)
        (eApex : TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids),
        Nonempty
          (eApex.hom ≫ toGroupoids.map f' ≅
            TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f ≫ eZ.hom) :=
  Iff.rfl

/-- The base of a 2-fibre product represented on spaces is equivalent to the
groupoid fibration of `G`. -/
theorem RepresentsTwoFibreProductOnSpace.exists_base {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {F G : AlgebraicSpace S} {f' : F ⟶ G}
    (h : RepresentsTwoFibreProductOnSpace f g F G f') :
    Nonempty (Z ≌ G.toGroupoids) :=
  by
    rcases h with ⟨eZ, eApex, h⟩
    exact ⟨eZ⟩

/-- The apex of a 2-fibre product represented on spaces is equivalent to the
groupoid fibration of `F`. -/
theorem RepresentsTwoFibreProductOnSpace.exists_apex {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {F G : AlgebraicSpace S} {f' : F ⟶ G}
    (h : RepresentsTwoFibreProductOnSpace f g F G f') :
    Nonempty
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids) :=
  by
    rcases h with ⟨eZ, eApex, h⟩
    exact ⟨eApex⟩

/-- The morphism of algebraic spaces recovers the first projection of the
2-fibre product up to the representing equivalences. -/
theorem RepresentsTwoFibreProductOnSpace.projection_triangle {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {F G : AlgebraicSpace S} {f' : F ⟶ G}
    (h : RepresentsTwoFibreProductOnSpace f g F G f') :
    ∃ (eZ : Z ≌ G.toGroupoids)
      (eApex : TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids),
      Nonempty
        (eApex.hom ≫ toGroupoids.map f' ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f ≫ eZ.hom) :=
  h

/-- Chosen representing equivalences and a 2-isomorphic projection triangle
yield a representation of the 2-fibre product on spaces. -/
theorem RepresentsTwoFibreProductOnSpace.of_equivalences {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {F G : AlgebraicSpace S} {f' : F ⟶ G}
    (eZ : Z ≌ G.toGroupoids)
    (eApex : TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids)
    (h : eApex.hom ≫ toGroupoids.map f' ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f ≫ eZ.hom) :
    RepresentsTwoFibreProductOnSpace f g F G f' :=
  ⟨eZ, eApex, ⟨h⟩⟩

/-- A supplied representing equivalence gives a comparison with explicit forward and inverse
fiber maps; no representative or quasi-inverse is selected. -/
private theorem exists_fiberIsoClassIso {S : Scheme.{u}}
    {X : GroupoidsOver S} {F : AlgebraicSpace S} (e : X ≌ F.toGroupoids) :
    ∃ i : Functor.fiberIsoClassPresheaf X.p ≅
        F.functorOfPoints ⋙ uliftFunctor.{u + 1, u},
      i.hom = BasedFunctor.fiberIsoClassMap (toBasedFunctor e.hom) ≫
        isoClassToPoints F := by
  letI : Functor.IsDiscreteFibration
      ((FiberedCategoryOver.Groupoids.toBased (Over S)).obj F.toGroupoids).p := by
    change Functor.IsDiscreteFibration ((CategoryOfElements.π F.functorOfPoints).leftOp)
    infer_instance
  let eB := (FiberedCategoryOver.Groupoids.toBased (Over S)).mapEquivalence e
  let eU (U : (Over S)ᵒᵖ) :=
    ((BasedCategory.Equivalence.fiberIsoClasses.equiv eB U.unop).trans
      (FiberedCategoryOver.Sets.ofPresheaf.fiberEquiv F.functorOfPoints U.unop)).trans
        Equiv.ulift.symm
  have heU (U : (Over S)ᵒᵖ) :
      (eU U).toIso.hom =
        (BasedFunctor.fiberIsoClassMap (toBasedFunctor e.hom) ≫
          isoClassToPoints F).app U := by
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl
  refine ⟨NatIso.ofComponents (fun U ↦ (eU U).toIso) ?_, ?_⟩
  · intro U V f
    simpa only [heU] using
      (BasedFunctor.fiberIsoClassMap (toBasedFunctor e.hom) ≫
        isoClassToPoints F).naturality f
  · apply NatTrans.ext
    funext U
    exact heU U

/-- Grothendieck fiber evaluation carries the induced map to the lifted morphism of spaces. -/
private theorem isoClassToPoints_map {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (f : F ⟶ G) :
    BasedFunctor.fiberIsoClassMap (toBasedFunctor (toGroupoids.map f)) ≫
        isoClassToPoints G =
      isoClassToPoints F ≫ Functor.whiskerRight f uliftFunctor.{u + 1, u} := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  let t := eqToHom (congrArg Opposite.op x.2)
  change ULift.up (G.functorOfPoints.map t (f.app _ x.1.unop.2)) =
    ULift.up (f.app U (F.functorOfPoints.map t x.1.unop.2))
  exact congrArg ULift.up
    (congrArg (fun k ↦ k x.1.unop.2) (f.naturality t)).symm

/-- The associated sheaves of isomorphism classes of the apex and of `Z` match
the functors of points of `F` and `G` after `uliftFunctor`, and
`BasedFunctor.fiberIsoClassMap` of `TwoFibreProduct.fst` corresponds to `f'`. -/
theorem RepresentsTwoFibreProductOnSpace.fiberIsoClass_ulift {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {F G : AlgebraicSpace S} {f' : F ⟶ G}
    (h : RepresentsTwoFibreProductOnSpace f g F G f') :
    ∃ (iZ : Functor.fiberIsoClassPresheaf Z.p ≅
        G.functorOfPoints ⋙ uliftFunctor.{u + 1, u})
      (iApex : Functor.fiberIsoClassPresheaf
          (p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f)) ≅
        F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}),
      BasedFunctor.fiberIsoClassMap
          (toBasedFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)) =
        iApex.hom ≫ Functor.whiskerRight f' uliftFunctor.{u + 1, u} ≫
          iZ.inv :=
  by
    rcases h with ⟨eZ, eApex, ⟨i⟩⟩
    obtain ⟨iZ, hiZ⟩ := exists_fiberIsoClassIso eZ
    obtain ⟨iApex, hiApex⟩ := exists_fiberIsoClassIso eApex
    refine ⟨iZ, iApex, ?_⟩
    apply (cancel_mono iZ.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hiZ, hiApex]
    have hi :
        BasedFunctor.fiberIsoClassMap (toBasedFunctor eApex.hom) ≫
            BasedFunctor.fiberIsoClassMap (toBasedFunctor (toGroupoids.map f')) =
          BasedFunctor.fiberIsoClassMap (toBasedFunctor (TwoFibreProduct.fst g f)) ≫
            BasedFunctor.fiberIsoClassMap (toBasedFunctor eZ.hom) := by
      simpa only [toBasedFunctor.comp, BasedFunctor.fiberIsoClassMap.comp] using
        BasedFunctor.fiberIsoClassMap.eq_of_hom i.hom.hom
    rw [← Category.assoc, ← hi, Category.assoc, isoClassToPoints_map,
      ← Category.assoc]

/-- A slice base change represented by an algebraic space over a scheme `U`
specializes the on-space comparison, with base representative `ofOver U`. -/
theorem RepresentsTwoFibreProductOnSpace.of_representsBaseChange
    {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y} {U : Over S}
    {y : GroupoidsOver.slice U ⟶ Y} {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    RepresentsTwoFibreProductOnSpace f y Fy (ofOver U) fy :=
  by
    rcases h with ⟨e, ⟨h⟩⟩
    let eU := ofOverSliceEquiv U
    refine ⟨eU.symm, e, ⟨?_⟩⟩
    exact (Bicategory.rightUnitor _).symm ≪≫
      Bicategory.whiskerLeftIso _ eU.unit ≪≫
      (Bicategory.associator _ _ _).symm ≪≫
      Bicategory.whiskerRightIso ((Bicategory.associator _ _ _) ≪≫ h) eU.inv

/-- Given algebraic-space representatives of the base and apex of a 2-fibre
product, its first projection corresponds to a morphism between those spaces.
The same morphism induces the canonical map on fiberwise isomorphism classes
under the lifted functors of points. -/
theorem RepresentsTwoFibreProductOnSpace.exists_morphism {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
    (F G : AlgebraicSpace S) (eZ : Z ≌ G.toGroupoids)
    (eApex : TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids) :
    ∃ f' : F ⟶ G,
      Nonempty
        (eApex.hom ≫ AlgebraicSpace.toGroupoids.map f' ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f ≫ eZ.hom) ∧
      ∃ (iZ : Functor.fiberIsoClassPresheaf Z.p ≅
          G.functorOfPoints ⋙ uliftFunctor.{u + 1, u})
        (iApex : Functor.fiberIsoClassPresheaf
            (FiberedCategoryOver.Groupoids.p
              (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f)) ≅
          F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}),
        BasedFunctor.fiberIsoClassMap
            (FiberedCategoryOver.Groupoids.toBasedFunctor
              (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)) =
          iApex.hom ≫ Functor.whiskerRight f' uliftFunctor.{u + 1, u} ≫ iZ.inv :=
  by
    let f' := toGroupoids.recover eApex eZ (TwoFibreProduct.fst g f)
    obtain ⟨i⟩ := toGroupoids.InducesHom.recover eApex eZ (TwoFibreProduct.fst g f)
    refine ⟨f', ⟨i.symm⟩, ?_⟩
    exact fiberIsoClass_ulift ⟨eZ, eApex, ⟨i.symm⟩⟩

end AlgebraicGeometry
