/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Algebra.Module.Congruence.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Closed

/-!
# Homotopy Category of a Differential Graded Category

This leaf forms the quotient of closed degree-zero morphisms by boundaries and
exposes the resulting homotopy category together with its localization functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {C : Type v}
variable [D : DifferentialGradedCategory R C]

open scoped DifferentialGradedCategory

/-- The object type of the homotopy category of a differential graded category. -/
@[stacks 09JQ, stacks 09L7]
inductive K (R : Type u) [CommRing R] (C : Type v) where
  | mk (obj : C)

namespace K

/-- The underlying differential graded object of a homotopy-category object. -/
def obj : K R C → C
  | ⟨X⟩ => X

/-- A `K` object can be used as its underlying object of the differential graded category. -/
instance : CoeTC (K R C) C where
  coe X := X.obj

/-- Constructing a `K` object and coercing it back recovers the original object. -/
@[simp] theorem coe_mk (X : C) : ((⟨X⟩ : K R C) : C) = X := rfl

end K

/-- Two closed degree-zero morphisms are homotopic when their difference is a boundary. -/
@[stacks 09JN]
def Homotopic (X Y : C) (f g : CompHom X Y) : Prop :=
  ∃ h : X ⟶[-1] Y, f.val - g.val = D.d (-1) h

/-- Homotopy of a closed degree-zero morphism with itself. -/
@[refl] theorem Homotopic.refl {X Y : C} (f : CompHom X Y) : Homotopic X Y f f := by
  let d : (X ⟶[-1] Y) →+ (X ⟶[0] Y) :=
    AddMonoidHom.mk' (D.d (-1)) (D.d_add (-1))
  refine ⟨0, ?_⟩
  change f.val - f.val = d 0
  rw [sub_self, map_zero]

/-- Homotopy is symmetric. -/
@[symm] theorem Homotopic.symm {X Y : C} {f g : CompHom X Y}
    (hfg : Homotopic X Y f g) : Homotopic X Y g f := by
  obtain ⟨h, hh⟩ := hfg
  refine ⟨-h, ?_⟩
  calc
    g.val - f.val = -(f.val - g.val) := (neg_sub _ _).symm
    _ = -D.d (-1) h := congrArg Neg.neg hh
    _ = D.d (-1) (-h) := by
      simpa only [neg_one_smul] using (D.d_smul (-1) (-1 : R) h).symm

/-- Homotopy is transitive. -/
@[trans] theorem Homotopic.trans {X Y : C} {f g h : CompHom X Y}
    (hfg : Homotopic X Y f g) (hgh : Homotopic X Y g h) : Homotopic X Y f h := by
  obtain ⟨a, ha⟩ := hfg
  obtain ⟨b, hb⟩ := hgh
  refine ⟨a + b, ?_⟩
  rw [D.d_add, ← ha, ← hb]
  exact (sub_add_sub_cancel _ _ _).symm

/-- Homotopy is an equivalence relation on each closed degree-zero hom-space. -/
theorem homotopy_equivalence (X Y : C) : Equivalence (Homotopic X Y) :=
  ⟨Homotopic.refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Homotopy is compatible with addition of closed degree-zero morphisms. -/
theorem Homotopic.add {X Y : C} {f₁ f₂ g₁ g₂ : CompHom X Y}
    (hf : Homotopic X Y f₁ f₂) (hg : Homotopic X Y g₁ g₂) :
    Homotopic X Y (f₁ + g₁) (f₂ + g₂) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a + b, ?_⟩
  change f₁.val + g₁.val - (f₂.val + g₂.val) = _
  rw [D.d_add, ← ha, ← hb]
  exact add_sub_add_comm _ _ _ _

/-- Homotopy is compatible with scalar multiplication of closed degree-zero morphisms. -/
theorem Homotopic.smul {X Y : C} (r : R) {f g : CompHom X Y}
    (hfg : Homotopic X Y f g) : Homotopic X Y (r • f) (r • g) := by
  obtain ⟨h, hh⟩ := hfg
  refine ⟨r • h, ?_⟩
  change r • f.val - r • g.val = _
  have hd : (D.d (-1) (r • h) : X ⟶[0] Y) = r • (D.d (-1) h : X ⟶[0] Y) :=
    D.d_smul (-1) r h
  rw [hd, ← hh]
  exact (smul_sub r f.val g.val).symm

/-- Homotopy is compatible with additive inverses of closed degree-zero morphisms. -/
theorem Homotopic.neg {X Y : C} {f g : CompHom X Y}
    (hfg : Homotopic X Y f g) : Homotopic X Y (-f) (-g) := by
  simpa only [neg_one_smul] using Homotopic.smul (-1 : R) hfg

/-- Homotopy is compatible with subtraction of closed degree-zero morphisms. -/
theorem Homotopic.sub {X Y : C} {f₁ f₂ g₁ g₂ : CompHom X Y}
    (hf : Homotopic X Y f₁ f₂) (hg : Homotopic X Y g₁ g₂) :
    Homotopic X Y (f₁ - g₁) (f₂ - g₂) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The `R`-module congruence on closed degree-zero morphisms induced by homotopy. -/
def homotopyModuleCon (X Y : C) : ModuleCon R (CompHom X Y) where
  toAddCon :=
    { r := Homotopic X Y
      iseqv := homotopy_equivalence X Y
      add' := fun hf hg ↦ Homotopic.add hf hg }
  smul r _ _ hfg := Homotopic.smul r hfg

/-- The canonical setoid identifying homotopic closed degree-zero morphisms. -/
def homotopySetoid (X Y : C) : Setoid (CompHom X Y) :=
  (homotopyModuleCon X Y).toSetoid

/-- The homotopy class of a closed degree-zero morphism. -/
abbrev HomotopyClass (X Y : C) :=
  (homotopyModuleCon X Y).Quotient

/-- Homotopy classes of closed degree-zero morphisms form an additive commutative group. -/
instance homotopyClassAddCommGroup (X Y : C) : AddCommGroup (HomotopyClass X Y) :=
  inferInstanceAs <| AddCommGroup (homotopyModuleCon X Y).Quotient

/-- Homotopy classes of closed degree-zero morphisms retain their canonical `R`-module structure. -/
instance homotopyClassModule (X Y : C) : Module R (HomotopyClass X Y) :=
  inferInstanceAs <| Module R (homotopyModuleCon X Y).Quotient

namespace CompHom

/-- A closed degree-zero morphism is homotopic to zero exactly when it is a boundary. -/
theorem homotopic_zero_iff {X Y : C} (f : CompHom X Y) :
    Homotopic X Y f 0 ↔ ∃ h : X ⟶[-1] Y, f.val = D.d (-1) h := by
  change (∃ h : X ⟶[-1] Y, f.val - 0 = D.d (-1) h) ↔ _
  simp only [sub_zero]

/-- The class of a closed degree-zero morphism in the homotopy category. -/
def toHomotopyClass {X Y : C} (f : CompHom X Y) : HomotopyClass X Y :=
  _root_.Quotient.mk (homotopySetoid X Y) f

/-- The class of the zero closed degree-zero morphism is zero. -/
@[simp] theorem toHomotopyClass_zero (X Y : C) :
    (0 : CompHom X Y).toHomotopyClass = 0 := rfl

/-- Passing to homotopy classes preserves addition. -/
@[simp] theorem toHomotopyClass_add {X Y : C} (f g : CompHom X Y) :
    (f + g).toHomotopyClass = f.toHomotopyClass + g.toHomotopyClass := rfl

/-- Passing to homotopy classes preserves additive inverses. -/
@[simp] theorem toHomotopyClass_neg {X Y : C} (f : CompHom X Y) :
    (-f).toHomotopyClass = -f.toHomotopyClass := rfl

/-- Passing to homotopy classes preserves subtraction. -/
@[simp] theorem toHomotopyClass_sub {X Y : C} (f g : CompHom X Y) :
    (f - g).toHomotopyClass = f.toHomotopyClass - g.toHomotopyClass := rfl

/-- Passing to homotopy classes preserves scalar multiplication. -/
@[simp] theorem toHomotopyClass_smul (r : R) {X Y : C} (f : CompHom X Y) :
    (r • f).toHomotopyClass = r • f.toHomotopyClass := rfl

/-- Equality of represented homotopy classes is exactly homotopy. -/
@[simp] theorem toHomotopyClass_eq_toHomotopyClass_iff {X Y : C} {f g : CompHom X Y} :
    f.toHomotopyClass = g.toHomotopyClass ↔ Homotopic X Y f g :=
  ⟨Quotient.exact, fun h ↦ Quotient.sound (s := homotopySetoid X Y) h⟩

/-- Homotopic closed morphisms define the same homotopy-class morphism. -/
theorem toHomotopyClass_eq_of_homotopic {X Y : C} {f g : CompHom X Y}
    (hfg : Homotopic X Y f g) : f.toHomotopyClass = g.toHomotopyClass :=
  toHomotopyClass_eq_toHomotopyClass_iff.mpr hfg

/-- Equality of represented homotopy-class morphisms yields a homotopy. -/
theorem homotopic_of_toHomotopyClass_eq {X Y : C} {f g : CompHom X Y}
    (hfg : f.toHomotopyClass = g.toHomotopyClass) : Homotopic X Y f g :=
  toHomotopyClass_eq_toHomotopyClass_iff.mp hfg

end CompHom

/-- The identity morphism in the homotopy category. -/
def kId (X : K R C) : HomotopyClass X.obj X.obj :=
  (CompHom.id X.obj).toHomotopyClass

/-- Composition of closed morphisms respects the homotopy relation. -/
theorem homotopy_comp_sound {X Y Z : C} {f₁ f₂ : CompHom X Y} {g₁ g₂ : CompHom Y Z}
    (hf : (homotopySetoid X Y).r f₁ f₂) (hg : (homotopySetoid Y Z).r g₁ g₂) :
    (homotopySetoid X Z).r (CompHom.comp f₁ g₁) (CompHom.comp f₂ g₂) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  let c : X ⟶[-1] Z := D.comp g₁.val a
  let e : X ⟶[-1] Z := D.comp b f₂.val
  refine ⟨c + e, ?_⟩
  let dXY : (X ⟶[-1] Y) →+ (X ⟶[0] Y) :=
    AddMonoidHom.mk' (D.d (-1)) (D.d_add (-1))
  let dYZ : (Y ⟶[-1] Z) →+ (Y ⟶[0] Z) :=
    AddMonoidHom.mk' (D.d (-1)) (D.d_add (-1))
  let dXZ : (X ⟶[-1] Z) →+ (X ⟶[0] Z) :=
    AddMonoidHom.mk' (D.d (-1)) (D.d_add (-1))
  let post : (X ⟶[0] Y) →+ (X ⟶[0] Z) :=
    AddMonoidHom.mk' (fun f ↦ D.comp g₁.val f) (D.comp_add_right g₁.val)
  let pre : (Y ⟶[0] Z) →+ (X ⟶[0] Z) :=
    AddMonoidHom.mk' (fun g ↦ D.comp g f₂.val) (fun g h ↦ D.comp_add_left g h f₂.val)
  let left : (Y ⟶[1] Z) →+ (X ⟶[0] Z) :=
    AddMonoidHom.mk' (fun g ↦ D.comp g a) (fun g h ↦ D.comp_add_left g h a)
  let right : (X ⟶[1] Y) →+ (X ⟶[0] Z) :=
    AddMonoidHom.mk' (fun f ↦ D.comp b f) (D.comp_add_right b)
  have hg₁ : D.d 0 g₁.val = 0 := g₁.property
  have hf₂ : D.d 0 f₂.val = 0 := f₂.property
  have hz₁ : left (D.d 0 g₁.val) = 0 :=
    (congrArg left hg₁).trans (map_zero left)
  have hz₂ : right (D.d 0 f₂.val) = 0 :=
    (congrArg right hf₂).trans (map_zero right)
  have hd₁ : dXZ c = post (dXY a) := by
    have hleib := D.d_comp g₁.val a
    change dXZ c = left (D.d 0 g₁.val) + ((0 : ℤ).negOnePow : R) • post (dXY a)
      at hleib
    simpa only [hz₁, Int.negOnePow_zero, Units.val_one,
      Int.cast_one, one_smul, zero_add] using hleib
  have hd₂ : dXZ e = pre (dYZ b) := by
    have hleib := D.d_comp b f₂.val
    change dXZ e = pre (dYZ b) + ((-1 : ℤ).negOnePow : R) • right (D.d 0 f₂.val)
      at hleib
    simpa only [hz₂, smul_zero, add_zero] using hleib
  change f₁.val - f₂.val = dXY a at ha
  change g₁.val - g₂.val = dYZ b at hb
  change post f₁.val - pre g₂.val = dXZ (c + e)
  rw [map_add, hd₁, hd₂, ← ha, ← hb]
  rw [map_sub, map_sub]
  exact (sub_add_sub_cancel _ _ _).symm

/-- Composition of homotopy classes. -/
def kComp {X Y Z : K R C} (f : HomotopyClass X.obj Y.obj)
    (g : HomotopyClass Y.obj Z.obj) : HomotopyClass X.obj Z.obj :=
  _root_.Quotient.map₂
    (fun f' g' ↦ CompHom.comp f' g')
    (fun _ _ hf _ _ hg ↦ homotopy_comp_sound hf hg)
    f g

/-- Left identity in the homotopy category. -/
theorem kCategory_id_comp {X Y : K R C} (f : HomotopyClass X.obj Y.obj) :
    kComp (kId X) f = f := by
  refine Quotient.inductionOn f ?_
  intro g
  change (CompHom.comp (CompHom.id X.obj) g).toHomotopyClass = g.toHomotopyClass
  apply congrArg CompHom.toHomotopyClass
  apply Subtype.ext
  exact D.comp_id_hom g.val

/-- Right identity in the homotopy category. -/
theorem kCategory_comp_id {X Y : K R C} (f : HomotopyClass X.obj Y.obj) :
    kComp f (kId Y) = f := by
  refine Quotient.inductionOn f ?_
  intro g
  change (CompHom.comp g (CompHom.id Y.obj)).toHomotopyClass = g.toHomotopyClass
  apply congrArg CompHom.toHomotopyClass
  apply Subtype.ext
  exact D.id_comp_hom g.val

/-- Associativity in the homotopy category. -/
theorem kCategory_assoc {W X Y Z : K R C} (f : HomotopyClass W.obj X.obj)
    (g : HomotopyClass X.obj Y.obj) (h : HomotopyClass Y.obj Z.obj) :
    kComp (kComp f g) h = kComp f (kComp g h) := by
  refine Quotient.inductionOn₃ f g h ?_
  intro a b c
  change (CompHom.comp (CompHom.comp a b) c).toHomotopyClass =
    (CompHom.comp a (CompHom.comp b c)).toHomotopyClass
  apply congrArg CompHom.toHomotopyClass
  apply Subtype.ext
  exact D.comp_assoc c.val b.val a.val

/-- The category structure on the homotopy category of a differential graded category. -/
@[reducible]
def kCategoryData : Category (K R C) where
  Hom X Y := HomotopyClass X.obj Y.obj
  id X := kId X
  comp f g := kComp f g
  id_comp := kCategory_id_comp
  comp_id := kCategory_comp_id
  assoc := kCategory_assoc

/-- The canonical category structure on the homotopy category of a differential graded category. -/
instance kCategory : Category (K R C) := kCategoryData

namespace K

/-- A homotopy-category object viewed as an object of the closed degree-zero category. -/
abbrev inComp (X : K R C) : Comp R C :=
  ⟨X.obj⟩

/-- The underlying DG object of `K.inComp` is unchanged. -/
@[simp] theorem inComp_obj (X : K R C) : (X.inComp : C) = X.obj := rfl

/-- Every homotopy-category morphism has a closed degree-zero representative. -/
theorem exists_rep {X Y : K R C} (f : X ⟶ Y) :
    ∃ g : CompHom X.obj Y.obj, f = g.toHomotopyClass := by
  exact Quotient.inductionOn f (fun g ↦ ⟨g, rfl⟩)

end K

namespace Comp

/-- A `Comp` object viewed in the homotopy category. -/
abbrev inK (X : Comp R C) : K R C :=
  ⟨X.obj⟩

/-- The underlying object of a `Comp` object is unchanged when viewed in `K`. -/
@[simp] theorem inK_obj (X : Comp R C) : (X.inK : C) = X.obj := rfl

/-- The image of an identity under the canonical quotient functor. -/
theorem inKFunctor_map_id (X : Comp R C) :
    (CompHom.id X.obj).toHomotopyClass = 𝟙 X.inK := rfl

/-- The image of a composite under the canonical quotient functor. -/
theorem inKFunctor_map_comp {X Y Z : Comp R C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CompHom.comp f g).toHomotopyClass =
      kComp (X := X.inK) (Y := Y.inK) (Z := Z.inK) f.toHomotopyClass g.toHomotopyClass := rfl

/-- The canonical quotient functor from closed degree-zero morphisms to homotopy classes. -/
@[stacks 09JQ]
abbrev inKFunctor : Comp R C ⥤ K R C where
  obj X := X.inK
  map f := f.toHomotopyClass
  map_id X := inKFunctor_map_id X
  map_comp f g := inKFunctor_map_comp f g

/-- The canonical quotient functor to the DG homotopy category is full. -/
theorem inKFunctor_full : (inKFunctor : Comp R C ⥤ K R C).Full := by
  constructor
  intro X Y f
  obtain ⟨g, hg⟩ := K.exists_rep f
  exact ⟨g, hg.symm⟩

/-- The canonical quotient functor to the DG homotopy category is essentially surjective. -/
theorem inKFunctor_essSurj : (inKFunctor : Comp R C ⥤ K R C).EssSurj := by
  constructor
  rintro ⟨X⟩
  exact ⟨⟨X⟩, ⟨Iso.refl _⟩⟩

/-- The morphisms of `Comp` which become isomorphisms in the homotopy category. -/
def homotopyEquivalences : MorphismProperty (Comp R C) :=
  fun _ _ f ↦ IsIso (inKFunctor.map f)

end Comp

namespace CompHom

/-- A closed degree-zero morphism viewed in the homotopy category. -/
abbrev inK {X Y : Comp R C} (f : X ⟶ Y) : X.inK ⟶ Y.inK :=
  f.toHomotopyClass

/-- Passing a `Comp` morphism to `K` is its represented homotopy class. -/
@[simp] theorem inK_eq_toHomotopyClass {X Y : Comp R C} (f : X ⟶ Y) :
    f.inK = f.toHomotopyClass := rfl

end CompHom

end DifferentialGradedCategory
