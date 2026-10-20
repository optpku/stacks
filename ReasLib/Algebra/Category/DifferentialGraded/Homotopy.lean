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
@[refl] theorem Homotopic.refl {X Y : C} (f : CompHom X Y) : Homotopic X Y f f := sorry

/-- Homotopy is symmetric. -/
@[symm] theorem Homotopic.symm {X Y : C} {f g : CompHom X Y}
    (hfg : Homotopic X Y f g) : Homotopic X Y g f := sorry

/-- Homotopy is transitive. -/
@[trans] theorem Homotopic.trans {X Y : C} {f g h : CompHom X Y}
    (hfg : Homotopic X Y f g) (hgh : Homotopic X Y g h) : Homotopic X Y f h := sorry

/-- Homotopy is an equivalence relation on each closed degree-zero hom-space. -/
theorem homotopy_equivalence (X Y : C) : Equivalence (Homotopic X Y) := sorry

/-- Homotopy is compatible with addition of closed degree-zero morphisms. -/
theorem Homotopic.add {X Y : C} {f₁ f₂ g₁ g₂ : CompHom X Y}
    (hf : Homotopic X Y f₁ f₂) (hg : Homotopic X Y g₁ g₂) :
    Homotopic X Y (f₁ + g₁) (f₂ + g₂) := sorry

/-- Homotopy is compatible with scalar multiplication of closed degree-zero morphisms. -/
theorem Homotopic.smul {X Y : C} (r : R) {f g : CompHom X Y}
    (hfg : Homotopic X Y f g) : Homotopic X Y (r • f) (r • g) := sorry

/-- Homotopy is compatible with additive inverses of closed degree-zero morphisms. -/
theorem Homotopic.neg {X Y : C} {f g : CompHom X Y}
    (hfg : Homotopic X Y f g) : Homotopic X Y (-f) (-g) := sorry

/-- Homotopy is compatible with subtraction of closed degree-zero morphisms. -/
theorem Homotopic.sub {X Y : C} {f₁ f₂ g₁ g₂ : CompHom X Y}
    (hf : Homotopic X Y f₁ f₂) (hg : Homotopic X Y g₁ g₂) :
    Homotopic X Y (f₁ - g₁) (f₂ - g₂) := sorry

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
    Homotopic X Y f 0 ↔ ∃ h : X ⟶[-1] Y, f.val = D.d (-1) h := sorry

/-- The class of a closed degree-zero morphism in the homotopy category. -/
def toHomotopyClass {X Y : C} (f : CompHom X Y) : HomotopyClass X Y :=
  _root_.Quotient.mk (homotopySetoid X Y) f

/-- The class of the zero closed degree-zero morphism is zero. -/
@[simp] theorem toHomotopyClass_zero (X Y : C) :
    (0 : CompHom X Y).toHomotopyClass = 0 := sorry

/-- Passing to homotopy classes preserves addition. -/
@[simp] theorem toHomotopyClass_add {X Y : C} (f g : CompHom X Y) :
    (f + g).toHomotopyClass = f.toHomotopyClass + g.toHomotopyClass := sorry

/-- Passing to homotopy classes preserves additive inverses. -/
@[simp] theorem toHomotopyClass_neg {X Y : C} (f : CompHom X Y) :
    (-f).toHomotopyClass = -f.toHomotopyClass := sorry

/-- Passing to homotopy classes preserves subtraction. -/
@[simp] theorem toHomotopyClass_sub {X Y : C} (f g : CompHom X Y) :
    (f - g).toHomotopyClass = f.toHomotopyClass - g.toHomotopyClass := sorry

/-- Passing to homotopy classes preserves scalar multiplication. -/
@[simp] theorem toHomotopyClass_smul (r : R) {X Y : C} (f : CompHom X Y) :
    (r • f).toHomotopyClass = r • f.toHomotopyClass := sorry

/-- Equality of represented homotopy classes is exactly homotopy. -/
@[simp] theorem toHomotopyClass_eq_toHomotopyClass_iff {X Y : C} {f g : CompHom X Y} :
    f.toHomotopyClass = g.toHomotopyClass ↔ Homotopic X Y f g := sorry

/-- Homotopic closed morphisms define the same homotopy-class morphism. -/
theorem toHomotopyClass_eq_of_homotopic {X Y : C} {f g : CompHom X Y}
    (hfg : Homotopic X Y f g) : f.toHomotopyClass = g.toHomotopyClass := sorry

/-- Equality of represented homotopy-class morphisms yields a homotopy. -/
theorem homotopic_of_toHomotopyClass_eq {X Y : C} {f g : CompHom X Y}
    (hfg : f.toHomotopyClass = g.toHomotopyClass) : Homotopic X Y f g := sorry

end CompHom

/-- The identity morphism in the homotopy category. -/
def kId (X : K R C) : HomotopyClass X.obj X.obj :=
  (CompHom.id X.obj).toHomotopyClass

/-- Composition of closed morphisms respects the homotopy relation. -/
theorem homotopy_comp_sound {X Y Z : C} {f₁ f₂ : CompHom X Y} {g₁ g₂ : CompHom Y Z}
    (hf : (homotopySetoid X Y).r f₁ f₂) (hg : (homotopySetoid Y Z).r g₁ g₂) :
    (homotopySetoid X Z).r (CompHom.comp f₁ g₁) (CompHom.comp f₂ g₂) := sorry

/-- Composition of homotopy classes. -/
def kComp {X Y Z : K R C} (f : HomotopyClass X.obj Y.obj)
    (g : HomotopyClass Y.obj Z.obj) : HomotopyClass X.obj Z.obj :=
  _root_.Quotient.map₂
    (fun f' g' ↦ CompHom.comp f' g')
    (fun _ _ hf _ _ hg ↦ homotopy_comp_sound hf hg)
    f g

/-- Left identity in the homotopy category. -/
theorem kCategory_id_comp {X Y : K R C} (f : HomotopyClass X.obj Y.obj) :
    kComp (kId X) f = f := sorry

/-- Right identity in the homotopy category. -/
theorem kCategory_comp_id {X Y : K R C} (f : HomotopyClass X.obj Y.obj) :
    kComp f (kId Y) = f := sorry

/-- Associativity in the homotopy category. -/
theorem kCategory_assoc {W X Y Z : K R C} (f : HomotopyClass W.obj X.obj)
    (g : HomotopyClass X.obj Y.obj) (h : HomotopyClass Y.obj Z.obj) :
    kComp (kComp f g) h = kComp f (kComp g h) := sorry

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
@[simp] theorem inComp_obj (X : K R C) : (X.inComp : C) = X.obj := sorry

/-- Every homotopy-category morphism has a closed degree-zero representative. -/
theorem exists_rep {X Y : K R C} (f : X ⟶ Y) :
    ∃ g : CompHom X.obj Y.obj, f = g.toHomotopyClass := sorry

end K

namespace Comp

/-- A `Comp` object viewed in the homotopy category. -/
abbrev inK (X : Comp R C) : K R C :=
  ⟨X.obj⟩

/-- The underlying object of a `Comp` object is unchanged when viewed in `K`. -/
@[simp] theorem inK_obj (X : Comp R C) : (X.inK : C) = X.obj := sorry

/-- The image of an identity under the canonical quotient functor. -/
theorem inKFunctor_map_id (X : Comp R C) :
    (CompHom.id X.obj).toHomotopyClass = 𝟙 X.inK := sorry

/-- The image of a composite under the canonical quotient functor. -/
theorem inKFunctor_map_comp {X Y Z : Comp R C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CompHom.comp f g).toHomotopyClass =
      kComp (X := X.inK) (Y := Y.inK) (Z := Z.inK) f.toHomotopyClass g.toHomotopyClass := sorry

/-- The canonical quotient functor from closed degree-zero morphisms to homotopy classes. -/
@[stacks 09JQ]
abbrev inKFunctor : Comp R C ⥤ K R C where
  obj X := X.inK
  map f := f.toHomotopyClass
  map_id X := inKFunctor_map_id X
  map_comp f g := inKFunctor_map_comp f g

/-- The canonical quotient functor to the DG homotopy category is full. -/
theorem inKFunctor_full : (inKFunctor : Comp R C ⥤ K R C).Full := sorry

/-- The canonical quotient functor to the DG homotopy category is essentially surjective. -/
theorem inKFunctor_essSurj : (inKFunctor : Comp R C ⥤ K R C).EssSurj := sorry

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
    f.inK = f.toHomotopyClass := sorry

end CompHom

end DifferentialGradedCategory
