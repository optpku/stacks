/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.GradedObject
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite

/-!
# Graded algebra sheaves

This leaf owns algebra objects graded by a small additive monoid in sheaves of modules over a
commutative ring sheaf on an arbitrary site.  It is deliberately stated for ringed sites rather
than ringed spaces, so it can be reused by both geometric and non-geometric applications.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddMonoid ι]

/-- An `ι`-graded algebra sheaf over `𝒪` consists of degreewise
`𝒪`-module sheaves, sectionwise multiplication, and a degree-zero unit compatible with
restriction, associativity, and the unit laws.  The default grading monoid is `ℤ`. -/
@[stacks 0FQW "graded algebra sheaves"]
structure GradedAlgebraSheaf (𝒪 : Sheaf J CommRingCat.{max u v})
    (ι : Type := ℤ) [AddMonoid ι] where
  /-- The degreewise family of `𝒪`-module sheaves. -/
  obj : ι → SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)
  /-- The degree-zero unit section. -/
  one : ∀ U : Cᵒᵖ, (obj 0).val.obj U
  /-- The degreewise multiplication on local sections. -/
  mul :
    ∀ (U : Cᵒᵖ) (n m : ι),
      (obj n).val.obj U →ₗ[𝒪.obj.obj U]
        (obj m).val.obj U →ₗ[𝒪.obj.obj U] (obj (n + m)).val.obj U
  /-- The unit section commutes with restriction maps. -/
  map_one :
    ∀ {U V : Cᵒᵖ} (f : U ⟶ V),
      ((obj 0).val.map f).hom (one U) = one V
  /-- The multiplication maps commute with restriction maps. -/
  map_mul :
    ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (n m : ι)
      (a : (obj n).val.obj U) (b : (obj m).val.obj U),
      ((obj (n + m)).val.map f).hom (mul U n m a b) =
        mul V n m (((obj n).val.map f).hom a) (((obj m).val.map f).hom b)
  /-- Multiplication is associative on local sections. -/
  mul_assoc :
    ∀ (U : Cᵒᵖ) (i j k : ι)
      (a : (obj i).val.obj U) (b : (obj j).val.obj U) (c : (obj k).val.obj U),
      HEq (mul U (i + j) k (mul U i j a b) c)
        (mul U i (j + k) a (mul U j k b c))
  /-- The unit acts as a left identity. -/
  one_mul :
    ∀ (U : Cᵒᵖ) (n : ι) (a : (obj n).val.obj U),
      HEq (mul U 0 n (one U) a) a
  /-- The unit acts as a right identity. -/
  mul_one :
    ∀ (U : Cᵒᵖ) (n : ι) (a : (obj n).val.obj U),
      HEq (mul U n 0 a (one U)) a

/-- A graded algebra sheaf evaluates to its degreewise module-sheaf family. -/
instance gradedAlgebraSheafCoeFun :
    CoeFun (GradedAlgebraSheaf 𝒪 ι)
      fun _ ↦ ι → SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪) where
  coe 𝒜 := 𝒜.obj

namespace GradedAlgebraSheaf

/-- The underlying graded object of module sheaves of a graded algebra sheaf. -/
abbrev toGradedObject (𝒜 : GradedAlgebraSheaf 𝒪 ι) :
    GradedObject ι (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) :=
  𝒜.obj

/-- A graded algebra sheaf coerces to its underlying graded object. -/
instance instCoeOut :
    CoeOut (GradedAlgebraSheaf 𝒪 ι)
      (GradedObject ι (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪))) where
  coe 𝒜 := 𝒜.toGradedObject

/-- The degree-`n` term of the underlying graded object is the degree-`n` module sheaf. -/
@[simp]
theorem toGradedObject_apply (𝒜 : GradedAlgebraSheaf 𝒪 ι) (n : ι) :
    𝒜.toGradedObject n = 𝒜 n := sorry

/-- The degree-`n` local sections of a graded algebra sheaf over an object of the site. -/
abbrev sections
    (𝒜 : GradedAlgebraSheaf 𝒪 ι)
    (U : Cᵒᵖ) (n : ι) : Type (max u v) :=
  (𝒜 n).val.obj U

/-- A homomorphism of graded algebra sheaves is a degreewise family of
`𝒪`-module sheaf morphisms compatible with the unit and multiplication. -/
structure Hom {𝒪 : Sheaf J CommRingCat.{max u v}}
    {ι : Type} [AddMonoid ι] (𝒜 ℬ : GradedAlgebraSheaf 𝒪 ι) where
  /-- The degreewise module-sheaf maps. -/
  hom : ∀ n : ι, 𝒜 n ⟶ ℬ n
  /-- The degree-zero map preserves the unit section. -/
  map_one :
    ∀ U : Cᵒᵖ,
      (((hom 0).val.app U).hom) (𝒜.one U) = ℬ.one U
  /-- The degreewise maps commute with multiplication on local sections. -/
  map_mul :
    ∀ (U : Cᵒᵖ) (n m : ι) (a : (𝒜 n).val.obj U) (b : (𝒜 m).val.obj U),
      (((hom (n + m)).val.app U).hom) (𝒜.mul U n m a b) =
        ℬ.mul U n m ((((hom n).val.app U).hom) a) ((((hom m).val.app U).hom) b)

/-- A graded algebra sheaf homomorphism evaluates degreewise. -/
instance gradedAlgebraSheafHomCoeFun {𝒪 : Sheaf J CommRingCat.{max u v}}
    (𝒜 ℬ : GradedAlgebraSheaf 𝒪 ι) :
    CoeFun (Hom 𝒜 ℬ) fun _ ↦ ∀ n : ι, 𝒜 n ⟶ ℬ n where
  coe f := f.hom

namespace Hom

/-- The identity homomorphism of a graded algebra sheaf. -/
def id (𝒜 : GradedAlgebraSheaf 𝒪 ι) : Hom 𝒜 𝒜 where
  hom := fun n ↦ 𝟙 (𝒜 n)
  map_one := sorry
  map_mul := sorry

/-- The composite of graded algebra sheaf homomorphisms. -/
def comp {𝒜 ℬ 𝒞 : GradedAlgebraSheaf 𝒪 ι} (f : Hom 𝒜 ℬ) (g : Hom ℬ 𝒞) : Hom 𝒜 𝒞 where
  hom := fun n ↦ f.hom n ≫ g.hom n
  map_one := sorry
  map_mul := sorry

/-- The degree-`n` component of the identity is the identity. -/
@[simp]
theorem id_hom (𝒜 : GradedAlgebraSheaf 𝒪 ι) (n : ι) :
    (id 𝒜).hom n = 𝟙 (𝒜 n) := sorry

/-- The degree-`n` component of a composite is the composite of degree-`n` components. -/
@[simp]
theorem comp_hom {𝒜 ℬ 𝒞 : GradedAlgebraSheaf 𝒪 ι}
    (f : Hom 𝒜 ℬ) (g : Hom ℬ 𝒞) (n : ι) :
    (comp f g).hom n = f.hom n ≫ g.hom n := sorry

end Hom

/-- Coercion of a graded algebra sheaf homomorphism recovers its degreewise component. -/
@[simp]
theorem coe_apply {𝒪 : Sheaf J CommRingCat.{max u v}}
    {𝒜 ℬ : GradedAlgebraSheaf 𝒪 ι} (f : Hom 𝒜 ℬ) (n : ι) :
    f n = f.hom n := sorry

/-- Two graded algebra sheaf homomorphisms are equal when their degreewise components agree. -/
@[ext]
theorem hom_ext {𝒪 : Sheaf J CommRingCat.{max u v}}
    {𝒜 ℬ : GradedAlgebraSheaf 𝒪 ι} (f g : Hom 𝒜 ℬ)
    (h : ∀ n : ι, f.hom n = g.hom n) : f = g := sorry

/-- Degreewise identities and compositions give graded algebra sheaves their category structure. -/
instance instCategory {𝒪 : Sheaf J CommRingCat.{max u v}} :
    Category (GradedAlgebraSheaf 𝒪 ι) where
  Hom 𝒜 ℬ := Hom 𝒜 ℬ
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The forgetful functor from graded algebra sheaves to their underlying graded module sheaves. -/
def forgetToGraded (𝒪 : Sheaf J CommRingCat.{max u v}) (ι : Type := ℤ) [AddMonoid ι] :
    GradedAlgebraSheaf 𝒪 ι ⥤
      GradedObject ι (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) where
  obj 𝒜 := 𝒜.toGradedObject
  map f := f.hom
  map_id := sorry
  map_comp := sorry

/-- Forgetting to the underlying graded object is faithful. -/
instance forgetToGraded_faithful (𝒪 : Sheaf J CommRingCat.{max u v}) (ι : Type := ℤ)
    [AddMonoid ι] :
    Functor.Faithful (forgetToGraded 𝒪 ι) where
  map_injective := sorry

/-- Forgetting a graded algebra sheaf recovers its underlying graded object. -/
@[simp]
theorem forgetToGraded_obj
    {𝒪 : Sheaf J CommRingCat.{max u v}} (𝒜 : GradedAlgebraSheaf 𝒪 ι) :
    (forgetToGraded 𝒪 ι).obj 𝒜 = 𝒜.toGradedObject := sorry

/-- Forgetting a graded algebra sheaf map recovers its underlying graded-object map. -/
@[simp]
theorem forgetToGraded_map
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    {𝒜 ℬ : GradedAlgebraSheaf 𝒪 ι} (f : 𝒜 ⟶ ℬ) :
    (forgetToGraded 𝒪 ι).map f = f.hom := sorry

/-- The forgotten graded object evaluates to the original degree-`n` module sheaf. -/
@[simp]
theorem forgetToGraded_obj_apply
    {𝒪 : Sheaf J CommRingCat.{max u v}} (𝒜 : GradedAlgebraSheaf 𝒪 ι) (n : ι) :
    ((forgetToGraded 𝒪 ι).obj 𝒜) n = 𝒜 n := sorry

/-- The forgotten graded-object map evaluates to the original degree-`n` component. -/
@[simp]
theorem forgetToGraded_map_apply
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    {𝒜 ℬ : GradedAlgebraSheaf 𝒪 ι} (f : 𝒜 ⟶ ℬ) (n : ι) :
    ((forgetToGraded 𝒪 ι).map f) n = f.hom n := sorry

end GradedAlgebraSheaf

end

end SheafOfModules.RingedSite
