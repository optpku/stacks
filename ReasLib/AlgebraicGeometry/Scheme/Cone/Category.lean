/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import ReasLib.AlgebraicGeometry.Scheme.Cone.Basic

/-!
# Explicit category operations for cones

This file supplies named identity and composition operations for cones over a fixed scheme and
packages them as an explicit category value.  It does not register a category instance.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

open SheafOfModules.RingedSite in
private theorem coneUnderlyingModuleMap_app {A B : S.QcAlgebraUnder} (f : A ⟶ B)
    (U : (TopologicalSpace.Opens S)ᵒᵖ) (a : (QcAlgebraUnder.sheaf S A).obj.obj U) :
    (((QcAlgebraUnder.underlyingModuleMap S f).val.app U).hom) a =
      ((f.hom.right.hom.app U).hom) a := by
  let α : QcAlgebraUnder.sheaf S A ⟶ QcAlgebraUnder.sheaf S B :=
    ((QcAlgebraUnder.forget S).map f).right
  let rawUnit :
      SheafOfModules.unit (ringSheaf (Opens.grothendieckTopology S) (QcAlgebraUnder.sheaf S A)) ⟶
        (restrictionAlong α).obj
          (SheafOfModules.unit (ringSheaf (Opens.grothendieckTopology S) (QcAlgebraUnder.sheaf S B))) := by
    let rawPush :=
      SheafOfModules.unitToPushforwardObjUnit
        (SheafOfModules.ChangeOfRings.homOverId (ringSheafMap (J := Opens.grothendieckTopology S) α))
    exact rawPush ≫
      (SheafOfModules.ChangeOfRings.pushforwardIso (ringSheafMap (J := Opens.grothendieckTopology S) α)).hom.app
        (SheafOfModules.unit (ringSheaf (Opens.grothendieckTopology S) (QcAlgebraUnder.sheaf S B)))
  let raw : QcAlgebraUnder.underlyingModule S A ⟶
      (restrictionAlong (A.obj.hom ≫ α)).obj (unitModule (Opens.grothendieckTopology S)
        (QcAlgebraUnder.sheaf S B)) :=
    (restrictionAlong A.obj.hom).map rawUnit
  have h (β : schemeCommRingSheaf S ⟶ QcAlgebraUnder.sheaf S B)
      (hβ : A.obj.hom ≫ α = β) :
      ((((hβ ▸ raw : QcAlgebraUnder.underlyingModule S A ⟶
        (restrictionAlong β).obj (unitModule (Opens.grothendieckTopology S)
          (QcAlgebraUnder.sheaf S B)))).val.app U).hom) a =
        ((α.hom.app U).hom) a := by
    subst β
    rfl
  exact h B.obj.hom f.hom.w

private theorem coneUnderlyingModuleMap_comp {A B C : S.QcAlgebraUnder} (f : A ⟶ B) (g : B ⟶ C) :
    QcAlgebraUnder.underlyingModuleMap S (f ≫ g) =
      QcAlgebraUnder.underlyingModuleMap S f ≫
        QcAlgebraUnder.underlyingModuleMap S g := by
  ext U a
  change (((QcAlgebraUnder.underlyingModuleMap S (f ≫ g)).val.app (Opposite.op U)).hom) a =
    (((QcAlgebraUnder.underlyingModuleMap S g).val.app (Opposite.op U)).hom)
      ((((QcAlgebraUnder.underlyingModuleMap S f).val.app (Opposite.op U)).hom) a)
  rw [coneUnderlyingModuleMap_app, coneUnderlyingModuleMap_app, coneUnderlyingModuleMap_app]
  rfl

private theorem coneGradedHom_comp {A B C : GradedQcAlgebra S}
    {f : A.algebra ⟶ B.algebra} {g : B.algebra ⟶ C.algebra}
    (hf : GradedQcAlgebra.IsGradedHom S f) (hg : GradedQcAlgebra.IsGradedHom S g) :
    GradedQcAlgebra.IsGradedHom S (f ≫ g) := by
  have hm := coneUnderlyingModuleMap_comp S f g
  have hd (n : ℕ) : GradedQcAlgebra.degreeMap S (f ≫ g) n =
      GradedQcAlgebra.degreeMap S f n ≫ GradedQcAlgebra.degreeMap S g n := by
    calc
      GradedQcAlgebra.degreeMap S (f ≫ g) n =
          (A.degreePieceToUnderlying n ≫ QcAlgebraUnder.underlyingModuleMap S f) ≫
            QcAlgebraUnder.underlyingModuleMap S g ≫ C.underlyingToDegreePiece n := by
        dsimp only [GradedQcAlgebra.degreeMap]
        rw [hm]
        simp only [Category.assoc]
      _ = (GradedQcAlgebra.degreeMap S f n ≫ B.degreePieceToUnderlying n) ≫
            QcAlgebraUnder.underlyingModuleMap S g ≫ C.underlyingToDegreePiece n := by
        rw [hf.2.2.1 n]
      _ = GradedQcAlgebra.degreeMap S f n ≫ GradedQcAlgebra.degreeMap S g n := by
        simp only [GradedQcAlgebra.degreeMap, Category.assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro U
    rw [hd]
    change (((GradedQcAlgebra.degreeMap S g 0).val.app U).hom)
      ((((GradedQcAlgebra.degreeMap S f 0).val.app U).hom) (A.one U)) = C.one U
    rw [hf.1 U, hg.1 U]
  · intro U n m a b
    rw [hd, hd, hd]
    change (((GradedQcAlgebra.degreeMap S g (n + m)).val.app U).hom)
        ((((GradedQcAlgebra.degreeMap S f (n + m)).val.app U).hom) (A.mul U n m a b)) =
      C.mul U n m
        ((((GradedQcAlgebra.degreeMap S g n).val.app U).hom)
          ((((GradedQcAlgebra.degreeMap S f n).val.app U).hom) a))
        ((((GradedQcAlgebra.degreeMap S g m).val.app U).hom)
          ((((GradedQcAlgebra.degreeMap S f m).val.app U).hom) b))
    rw [hf.2.1 U n m a b, hg.2.1]
  · intro n
    rw [hd, hm]
    calc
      (GradedQcAlgebra.degreeMap S f n ≫ GradedQcAlgebra.degreeMap S g n) ≫
          C.degreePieceToUnderlying n =
        GradedQcAlgebra.degreeMap S f n ≫
          (GradedQcAlgebra.degreeMap S g n ≫ C.degreePieceToUnderlying n) :=
        Category.assoc _ _ _
      _ = GradedQcAlgebra.degreeMap S f n ≫
          (B.degreePieceToUnderlying n ≫ QcAlgebraUnder.underlyingModuleMap S g) := by
        rw [hg.2.2.1 n]
      _ = (GradedQcAlgebra.degreeMap S f n ≫ B.degreePieceToUnderlying n) ≫
          QcAlgebraUnder.underlyingModuleMap S g := (Category.assoc _ _ _).symm
      _ = (A.degreePieceToUnderlying n ≫ QcAlgebraUnder.underlyingModuleMap S f) ≫
          QcAlgebraUnder.underlyingModuleMap S g := by
        rw [hf.2.2.1 n]
      _ = A.degreePieceToUnderlying n ≫
          (QcAlgebraUnder.underlyingModuleMap S f ≫ QcAlgebraUnder.underlyingModuleMap S g) :=
        Category.assoc _ _ _
  · intro n
    rw [hd, hm]
    calc
      (QcAlgebraUnder.underlyingModuleMap S f ≫ QcAlgebraUnder.underlyingModuleMap S g) ≫
          C.underlyingToDegreePiece n =
        QcAlgebraUnder.underlyingModuleMap S f ≫
          (QcAlgebraUnder.underlyingModuleMap S g ≫ C.underlyingToDegreePiece n) :=
        Category.assoc _ _ _
      _ = QcAlgebraUnder.underlyingModuleMap S f ≫
          (B.underlyingToDegreePiece n ≫ GradedQcAlgebra.degreeMap S g n) := by
        rw [hg.2.2.2.1 n]
      _ = (QcAlgebraUnder.underlyingModuleMap S f ≫ B.underlyingToDegreePiece n) ≫
          GradedQcAlgebra.degreeMap S g n := (Category.assoc _ _ _).symm
      _ = (A.underlyingToDegreePiece n ≫ GradedQcAlgebra.degreeMap S f n) ≫
          GradedQcAlgebra.degreeMap S g n := by
        rw [hf.2.2.2.1 n]
      _ = A.underlyingToDegreePiece n ≫
          (GradedQcAlgebra.degreeMap S f n ≫ GradedQcAlgebra.degreeMap S g n) :=
        Category.assoc _ _ _
  · rw [hd, Category.assoc, hg.2.2.2.2, hf.2.2.2.2]

private theorem coneGradedHom_id (A : GradedQcAlgebra S) : GradedQcAlgebra.IsGradedHom S (𝟙 A.algebra) := by
  have hd (n : ℕ) : GradedQcAlgebra.degreeMap S (𝟙 A.algebra) n = 𝟙 (A.degreePiece n) := by
    change A.degreePieceToUnderlying n ≫ 𝟙 _ ≫ A.underlyingToDegreePiece n = 𝟙 _
    simpa using A.degreePiece_split n
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro U
    rw [hd]
    rfl
  · intro U n m a b
    rw [hd, hd, hd]
    rfl
  · intro n
    rw [hd]
    change 𝟙 _ ≫ A.degreePieceToUnderlying n = A.degreePieceToUnderlying n ≫ 𝟙 _
    simp
  · intro n
    rw [hd]
    change 𝟙 _ ≫ A.underlyingToDegreePiece n = A.underlyingToDegreePiece n ≫ 𝟙 _
    simp
  · rw [hd]
    exact Category.id_comp _

namespace ConeHom

/-- The identity scheme morphism of a cone lies over the base. -/
theorem idOverBase (X : ConeOver S) :
    (𝟙 X.C) ≫ X.π = X.π := by
  exact Category.id_comp X.π

end ConeHom

namespace ConeOver

/-- Transporting the identity pullback through the chosen algebra identification gives the
identity chosen-algebra morphism. -/
theorem chosenAlgebraPullback_id (X : ConeOver S) :
    chosenAlgebraPullback S (𝟙 X.C) (ConeHom.idOverBase S X) =
      𝟙 X.pushforwardGrading.algebra := by
  apply ObjectProperty.hom_ext
  exact X.pushforwardAlgebraIso.hom_inv_id

end ConeOver


namespace ConeHom

/-- The identity scheme morphism is compatible with the explicit grading. -/
theorem idCompatibleWithGrading (X : ConeOver S) :
    coneHomCompatibleWithGrading S (𝟙 X.C) (idOverBase S X) := by
  change GradedQcAlgebra.IsGradedHom S
    (ConeOver.chosenAlgebraPullback S (𝟙 X.C) (idOverBase S X))
  rw [ConeOver.chosenAlgebraPullback_id]
  exact coneGradedHom_id S X.pushforwardGrading

/-- The identity morphism of a cone. -/
def id (X : ConeOver S) : ConeHom S X X where
  hom := 𝟙 X.C
  overBase := idOverBase S X
  compatibleWithGrading := idCompatibleWithGrading S X

/-- The composite of two underlying scheme morphisms lies over the base. -/
theorem compOverBase {X Y Z : ConeOver S}
    (f : ConeHom S X Y) (g : ConeHom S Y Z) :
    (f.hom ≫ g.hom) ≫ Z.π = X.π := by
  rw [Category.assoc, g.overBase, f.overBase]

end ConeHom

namespace ConeOver

private theorem inducedPullback_comp {X Y Z : ConeOver S}
    (f : ConeHom S X Y) (g : ConeHom S Y Z) :
    inducedConePushforwardPullback S (f.hom ≫ g.hom) (ConeHom.compOverBase S f g) =
      inducedConePushforwardPullback S g.hom g.overBase ≫
        inducedConePushforwardPullback S f.hom f.overBase := by
  have h : ∀ (p : X.C ⟶ S) (q : Y.C ⟶ S) (r : Z.C ⟶ S)
      (hf : f.hom ≫ q = p) (hg : g.hom ≫ r = q)
      (hfg : (f.hom ≫ g.hom) ≫ r = p),
      (hfg ▸ Under.homMk
        ((TopCat.Sheaf.pushforward CommRingCat.{u} r.1.base).map
          (RingedSpace.Hom.commRingSheafPushforwardMap (f.hom ≫ g.hom).toShHom)) rfl :
        Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap r.toShHom) ⟶
          Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap p.toShHom)) =
      (hg ▸ Under.homMk
        ((TopCat.Sheaf.pushforward CommRingCat.{u} r.1.base).map
          (RingedSpace.Hom.commRingSheafPushforwardMap g.hom.toShHom)) rfl :
        Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap r.toShHom) ⟶
          Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap q.toShHom)) ≫
      (hf ▸ Under.homMk
        ((TopCat.Sheaf.pushforward CommRingCat.{u} q.1.base).map
          (RingedSpace.Hom.commRingSheafPushforwardMap f.hom.toShHom)) rfl :
        Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap q.toShHom) ⟶
          Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap p.toShHom)) := by
    intro p q r hf hg hfg
    subst p
    subst q
    rfl
  exact h X.π Y.π Z.π f.overBase g.overBase (ConeHom.compOverBase S f g)

/-- Pullback on chosen algebras reverses composition of cone maps. -/
theorem chosenAlgebraPullback_comp {X Y Z : ConeOver S}
    (f : ConeHom S X Y) (g : ConeHom S Y Z) :
    chosenAlgebraPullback S (f.hom ≫ g.hom) (ConeHom.compOverBase S f g) =
      chosenAlgebraPullback S g.hom g.overBase ≫
        chosenAlgebraPullback S f.hom f.overBase := by
  apply ObjectProperty.hom_ext
  change Z.pushforwardAlgebraIso.hom ≫
      inducedConePushforwardPullback S (f.hom ≫ g.hom) (ConeHom.compOverBase S f g) ≫
        X.pushforwardAlgebraIso.inv =
      (Z.pushforwardAlgebraIso.hom ≫ inducedConePushforwardPullback S g.hom g.overBase ≫
        Y.pushforwardAlgebraIso.inv) ≫
      (Y.pushforwardAlgebraIso.hom ≫ inducedConePushforwardPullback S f.hom f.overBase ≫
        X.pushforwardAlgebraIso.inv)
  rw [inducedPullback_comp S f g]
  exact (congrArg
    (fun k => Z.pushforwardAlgebraIso.hom ≫
      inducedConePushforwardPullback S g.hom g.overBase ≫ k ≫
        inducedConePushforwardPullback S f.hom f.overBase ≫ X.pushforwardAlgebraIso.inv)
    Y.pushforwardAlgebraIso.inv_hom_id).symm

end ConeOver


namespace ConeHom

/-- The composite of two cone morphisms is compatible with the explicit gradings. -/
theorem compCompatibleWithGrading {X Y Z : ConeOver S}
    (f : ConeHom S X Y) (g : ConeHom S Y Z) :
    coneHomCompatibleWithGrading S (f.hom ≫ g.hom) (compOverBase S f g) := by
  change GradedQcAlgebra.IsGradedHom S
    (ConeOver.chosenAlgebraPullback S (f.hom ≫ g.hom) (compOverBase S f g))
  rw [ConeOver.chosenAlgebraPullback_comp]
  exact coneGradedHom_comp S g.compatibleWithGrading f.compatibleWithGrading

/-- Composition of explicit cone morphisms. -/
def comp {X Y Z : ConeOver S} (f : ConeHom S X Y) (g : ConeHom S Y Z) :
    ConeHom S X Z where
  hom := f.hom ≫ g.hom
  overBase := compOverBase S f g
  compatibleWithGrading := compCompatibleWithGrading S f g

/-- Cone morphisms are equal when their underlying scheme morphisms are equal. -/
theorem ext {X Y : ConeOver S} {f g : ConeHom S X Y} (h : f.hom = g.hom) :
    f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Left identity for explicit cone morphisms. -/
theorem id_comp {X Y : ConeOver S} (f : ConeHom S X Y) :
    comp S (id S X) f = f := by
  apply ext S
  exact Category.id_comp f.hom

/-- Right identity for explicit cone morphisms. -/
theorem comp_id {X Y : ConeOver S} (f : ConeHom S X Y) :
    comp S f (id S Y) = f := by
  apply ext S
  exact Category.comp_id f.hom

/-- Associativity of explicit cone-morphism composition. -/
theorem assoc {W X Y Z : ConeOver S}
    (f : ConeHom S W X) (g : ConeHom S X Y) (h : ConeHom S Y Z) :
    comp S (comp S f g) h = comp S f (comp S g h) := by
  apply ext S
  exact Category.assoc f.hom g.hom h.hom

end ConeHom

/-- The category structure carried explicitly by cones over `S`. -/
@[reducible]
def coneCategory : Category (ConeOver S) where
  Hom X Y := ConeHom S X Y
  id := ConeHom.id S
  comp f g := ConeHom.comp S f g
  id_comp := ConeHom.id_comp S
  comp_id := ConeHom.comp_id S
  assoc := ConeHom.assoc S

/-- The bundled category of cones over `S`. -/
def coneCat : Cat :=
  ⟨ConeOver S, coneCategory S⟩

end AlgebraicGeometry.Scheme
