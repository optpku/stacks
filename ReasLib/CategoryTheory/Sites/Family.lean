/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-target indexed families of arrows

This module supplies the small data model shared by site-theoretic constructions which use an
indexed family of arrows into one object.  A family is represented as an indexed family in the
slice category, with canonical presieve and sieve views.
-/

@[expose] public section

universe w₃ w₂ w₁ w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {U : C}

namespace SemiRepresentableFamily

namespace Over

/-- An indexed family of arrows in `C` with a fixed common target `U`. -/
@[stacks 0396 "fixed-target indexed family",
  stacks 01G0 "semi-representable family over an object"]
structure Obj (U : C) where
  index : Type w
  obj : index → CategoryTheory.Over U

/-- A reindexing map between fixed-target families, together with component maps in `C / U`. -/
@[stacks 00VT "morphism of fixed-target families",
  stacks 01G0 "morphism of semi-representable families over an object"]
structure Hom {U : C} (𝒰 : Obj.{w₁} U) (𝒱 : Obj.{w₂} U) where
  α : 𝒰.index → 𝒱.index
  f : ∀ i : 𝒰.index, 𝒰.obj i ⟶ 𝒱.obj (α i)

/-- The identity componentwise reindexing of a fixed-target family. -/
@[stacks 00VT "identity morphism of fixed-target families"]
def Hom.id (𝒰 : Obj.{w} U) : Hom 𝒰 𝒰 where
  α := fun i ↦ i
  f := fun i ↦ 𝟙 (𝒰.obj i)

/-- Compose componentwise reindexings whose index types may lie in different universes. -/
@[stacks 00VT "composition of fixed-target family morphisms"]
def Hom.comp {𝒰 : Obj.{w₁} U} {𝒱 : Obj.{w₂} U} {𝒲 : Obj.{w₃} U}
    (φ : Hom 𝒰 𝒱) (ψ : Hom 𝒱 𝒲) : Hom 𝒰 𝒲 where
  α := fun i ↦ ψ.α (φ.α i)
  f := fun i ↦ φ.f i ≫ ψ.f (φ.α i)

/-- Composing the identity reindexing with a family morphism leaves that morphism unchanged. -/
theorem Hom.id_comp {𝒰 : Obj.{w₁} U} {𝒱 : Obj.{w₂} U} (φ : Hom 𝒰 𝒱) :
    Hom.comp (Hom.id 𝒰) φ = φ := by
  cases φ
  simp [Hom.comp, Hom.id]

/-- Composing a family morphism with the identity reindexing leaves that morphism unchanged. -/
theorem Hom.comp_id {𝒰 : Obj.{w₁} U} {𝒱 : Obj.{w₂} U} (φ : Hom 𝒰 𝒱) :
    Hom.comp φ (Hom.id 𝒱) = φ := by
  cases φ
  simp [Hom.comp, Hom.id]

/-- Composition of componentwise reindexings of fixed-target families is associative. -/
theorem Hom.assoc {𝒰 : Obj.{w} U} {𝒱 : Obj.{w₁} U}
    {𝒲 : Obj.{w₂} U} {𝒵 : Obj.{w₃} U}
    (φ : Hom 𝒰 𝒱) (ψ : Hom 𝒱 𝒲) (χ : Hom 𝒲 𝒵) :
    Hom.comp (Hom.comp φ ψ) χ = Hom.comp φ (Hom.comp ψ χ) := by
  cases φ
  cases ψ
  cases χ
  simp [Hom.comp, Category.assoc]

/-- Fixed-target families form the category whose morphisms reindex the family and
provide a slice morphism at every component. -/
@[stacks 01G0 "category of semi-representable families over an object",
  stacks 01G0 "quiver of semi-representable families over an object"]
def category (U : C) : Cat.{max w v, max (w + 1) u v} :=
  ⟨Obj.{w} U, {
    Hom := fun 𝒰 𝒱 ↦ Hom 𝒰 𝒱
    id := fun 𝒰 ↦ Hom.id 𝒰
    comp := fun φ ψ ↦ Hom.comp φ ψ
    id_comp := Hom.id_comp
    comp_id := Hom.comp_id
    assoc := Hom.assoc
  }⟩

end Over

/-- The carrier of the category of indexed families of arrows with common target `U`. -/
abbrev Over (U : C) : Type (max (w + 1) u v) := Over.category.{w} U

namespace Over

/-- The index type of a fixed-target family of arrows. -/
abbrev index (𝒰 : SemiRepresentableFamily.Over.{w} U) : Type w := Obj.index 𝒰

/-- The slice object of a fixed-target family at a specified index. -/
abbrev obj (𝒰 : SemiRepresentableFamily.Over.{w} U) (i : 𝒰.index) :
    CategoryTheory.Over U := Obj.obj 𝒰 i

/-- Construct a fixed-target family from an index type and its slice objects. -/
def mk (index : Type w) (obj : index → CategoryTheory.Over U) :
    SemiRepresentableFamily.Over.{w} U := ⟨index, obj⟩

/-- The underlying component of a composite family morphism is the composite of the underlying
component morphisms. -/
@[simp, stacks 01G0 "composition readout for family morphisms"]
theorem Hom.comp_left {U : C} {𝒰 𝒱 𝒲 : SemiRepresentableFamily.Over.{w} U}
    (φ : 𝒰 ⟶ 𝒱) (ψ : 𝒱 ⟶ 𝒲) (i : 𝒰.index) :
    ((φ ≫ ψ).f i).left = (φ.f i).left ≫ (ψ.f (φ.α i)).left := rfl

/-- Build a fixed-target family from an explicit indexed family of arrows. -/
@[stacks 0396 "family built from explicit arrows"]
def ofArrows {I : Type w₁} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) :
    SemiRepresentableFamily.Over.{w₁} U where
  index := I
  obj := fun i ↦ CategoryTheory.Over.mk (π i)

/-- The singleton fixed-target family associated to one arrow. -/
@[stacks 0396 "singleton fixed-target family"]
def singleton {V : C} (f : V ⟶ U) : SemiRepresentableFamily.Over.{w₁} U :=
  ofArrows (fun _ : PUnit.{w₁ + 1} ↦ V) (fun _ : PUnit.{w₁ + 1} ↦ f)

/-- The source of the unique member of a singleton family is the source of its arrow. -/
@[simp, stacks 0396 "singleton-family source readout"]
theorem singleton_obj_left {V : C} (f : V ⟶ U) (i : (singleton f).index) :
    ((singleton f).obj i).left = V := rfl

/-- The structure map of the unique member of a singleton family is its defining arrow. -/
@[simp, stacks 0396 "singleton-family arrow readout"]
theorem singleton_obj_hom {V : C} (f : V ⟶ U) (i : (singleton f).index) :
    ((singleton f).obj i).hom = f := rfl

/-- A family built from arrows has the corresponding slice object at each index. -/
@[simp, stacks 0396 "explicit-family object readout"]
theorem ofArrows_obj {I : Type w₁} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) (i : I) :
    (ofArrows Uᵢ π).obj i = CategoryTheory.Over.mk (π i) := rfl

/-- The source of a member of a family built from arrows is its specified source. -/
@[simp, stacks 0396 "explicit-family source readout"]
theorem ofArrows_obj_left {I : Type w₁} (Uᵢ : I → C)
    (π : ∀ i : I, Uᵢ i ⟶ U) (i : I) :
    ((ofArrows Uᵢ π).obj i).left = Uᵢ i := rfl

/-- The structure map of a member of a family built from arrows is the specified arrow. -/
@[simp, stacks 0396 "explicit-family arrow readout"]
theorem ofArrows_obj_hom {I : Type w₁} (Uᵢ : I → C)
    (π : ∀ i : I, Uᵢ i ⟶ U) (i : I) :
    ((ofArrows Uᵢ π).obj i).hom = π i := rfl

/-- Flatten a family over `U` together with a family over each of its source objects. -/
@[stacks 0396 "composition of fixed-target families"]
def bind (𝒰 : SemiRepresentableFamily.Over.{w₁} U)
    (𝒱 : ∀ i : 𝒰.index, SemiRepresentableFamily.Over.{w₂} (𝒰.obj i).left) :
    SemiRepresentableFamily.Over.{max w₁ w₂} U :=
  ofArrows
    (fun ij : Σ i, (𝒱 i).index ↦ ((𝒱 ij.1).obj ij.2).left)
    (fun ij ↦ ((𝒱 ij.1).obj ij.2).hom ≫ (𝒰.obj ij.1).hom)

/-- The source of a member of `𝒰.bind 𝒱` is the corresponding source in `𝒱`. -/
@[simp, stacks 0396 "composed-family source readout"]
theorem bind_obj_left (𝒰 : SemiRepresentableFamily.Over.{w₁} U)
    (𝒱 : ∀ i : 𝒰.index, SemiRepresentableFamily.Over.{w₂} (𝒰.obj i).left)
    (ij : (𝒰.bind 𝒱).index) :
    ((𝒰.bind 𝒱).obj ij).left = ((𝒱 ij.1).obj ij.2).left := rfl

/-- The arrow of a member of `𝒰.bind 𝒱` is the corresponding composite arrow. -/
@[simp, stacks 0396 "composed-family arrow readout"]
theorem bind_obj_hom (𝒰 : SemiRepresentableFamily.Over.{w₁} U)
    (𝒱 : ∀ i : 𝒰.index, SemiRepresentableFamily.Over.{w₂} (𝒰.obj i).left)
    (ij : (𝒰.bind 𝒱).index) :
    ((𝒰.bind 𝒱).obj ij).hom =
      ((𝒱 ij.1).obj ij.2).hom ≫ (𝒰.obj ij.1).hom := rfl

/-- Apply a functor of slice categories componentwise to a fixed-target family. -/
def map {U V : C}
    (F : CategoryTheory.Over U ⥤ CategoryTheory.Over V)
    (𝒰 : SemiRepresentableFamily.Over.{w₁} U) :
    SemiRepresentableFamily.Over.{w₁} V where
  index := 𝒰.index
  obj := fun i ↦ F.obj (𝒰.obj i)

/-- The members of a componentwise-mapped family are the corresponding images. -/
@[simp]
theorem map_obj {U V : C}
    (F : CategoryTheory.Over U ⥤ CategoryTheory.Over V)
    (𝒰 : SemiRepresentableFamily.Over.{w₁} U) (i : 𝒰.index) :
    (map F 𝒰).obj i = F.obj (𝒰.obj i) := rfl

/-- The structure map of a componentwise-mapped family is the structure map of the corresponding
image in the target slice category. -/
@[simp]
theorem map_obj_hom {U V : C}
    (F : CategoryTheory.Over U ⥤ CategoryTheory.Over V)
    (𝒰 : SemiRepresentableFamily.Over.{w₁} U) (i : 𝒰.index) :
    ((map F 𝒰).obj i).hom = (F.obj (𝒰.obj i)).hom := rfl

/-- A morphism from a base-changed family has component maps compatible with the base map. -/
@[stacks 00VT "family-morphism base compatibility"]
theorem Hom.map_hom {U V : C}
    {𝒰 : SemiRepresentableFamily.Over.{w₁} U}
    {𝒱 : SemiRepresentableFamily.Over.{w₂} V}
    (base : U ⟶ V)
    (φ : Hom (SemiRepresentableFamily.Over.map (CategoryTheory.Over.map base) 𝒰) 𝒱)
    (i : 𝒰.index) :
    (φ.f i).left ≫ (𝒱.obj (φ.α i)).hom = (𝒰.obj i).hom ≫ base := by
  exact CategoryTheory.Over.w (φ.f i)

/-- The component maps of a morphism between families over the same target commute with the
structure maps, written in the identity-base form used by pullback constructions. -/
@[stacks 00VT "same-target family-morphism compatibility"]
theorem Hom.map_hom_id {U : C}
    {𝒰 : SemiRepresentableFamily.Over.{w₁} U}
    {𝒱 : SemiRepresentableFamily.Over.{w₂} U}
    (φ : Hom 𝒰 𝒱) (i : 𝒰.index) :
    (φ.f i).left ≫ (𝒱.obj (φ.α i)).hom = (𝒰.obj i).hom ≫ 𝟙 U := by
  simpa only [Category.comp_id] using CategoryTheory.Over.w (φ.f i)

/-- The presieve generated by a fixed-target indexed family. -/
abbrev toPresieve (𝒰 : Over.{w} U) : Presieve U :=
  Presieve.ofArrows (fun i ↦ (𝒰.obj i).left) fun i ↦ (𝒰.obj i).hom

/-- Pairwise pullbacks for the presieve generated by a family are available componentwise to
typeclass search. -/
instance pairwiseHasPullback (𝒰 : Over.{w} U)
    [𝒰.toPresieve.HasPairwisePullbacks] (i j : 𝒰.index) :
    Limits.HasPullback (𝒰.obj i).hom (𝒰.obj j).hom :=
  Presieve.HasPairwisePullbacks.has_pullbacks
    (R := 𝒰.toPresieve) (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j)

/-- The presieve view of a family built from explicit arrows is the original presieve. -/
@[simp]
theorem toPresieve_ofArrows {I : Type w₁} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) :
    toPresieve (ofArrows Uᵢ π) = Presieve.ofArrows Uᵢ π := rfl

/-- Reindexing an explicit family along `ULift.down` does not change its generated presieve. -/
@[simp]
theorem toPresieve_ofArrows_ulift {I : Type w₁} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) :
    toPresieve (ofArrows (fun i : ULift.{w₂} I ↦ Uᵢ i.down) fun i ↦ π i.down) =
      Presieve.ofArrows Uᵢ π := by
  exact Presieve.ofArrows_comp_eq_of_surjective π
    (fun i ↦ ⟨ULift.up i, rfl⟩)

/-- The sieve generated by a fixed-target indexed family. -/
@[stacks 00Z1 "sieve generated by a fixed-target family"]
abbrev toSieve (𝒰 : Over.{w} U) : Sieve U :=
  Sieve.generate (toPresieve 𝒰)

/-- The sieve view of a family built from explicit arrows is the original generated sieve. -/
@[simp, stacks 00Z1 "explicit-family sieve readout"]
theorem toSieve_ofArrows {I : Type w₁} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) :
    toSieve (ofArrows Uᵢ π) = Sieve.ofArrows Uᵢ π := rfl

/-- Reindexing an explicit family along `ULift.down` does not change its generated sieve. -/
@[simp, stacks 00Z1 "lifted explicit-family sieve readout"]
theorem toSieve_ofArrows_ulift {I : Type w₁} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) :
    toSieve (ofArrows (fun i : ULift.{w₂} I ↦ Uᵢ i.down) fun i ↦ π i.down) =
      Sieve.ofArrows Uᵢ π := by
  exact congrArg Sieve.generate (toPresieve_ofArrows_ulift Uᵢ π)

end Over
end SemiRepresentableFamily

namespace Presieve

/-- The family indexed by all arrows in a presieve generates that presieve. -/
theorem ofArrows_uncurry_eq {U : C} (R : Presieve U) :
    Presieve.ofArrows
      (fun i : R.uncurry ↦ (CategoryTheory.Over.mk i.1.2).left)
      (fun i ↦ (CategoryTheory.Over.mk i.1.2).hom) = R := by
  refine le_antisymm ?_ ?_
  · rintro _ _ ⟨i⟩
    exact i.2
  · intro X f hf
    exact Presieve.ofArrows.mk (⟨⟨X, f⟩, hf⟩ : R.uncurry)

/-- A specified indexed family of arrows which generates a presieve.  Keeping the family as
data, rather than only asserting the existence of its arrows, lets later constructions reuse the
chosen cover index. -/
structure GeneratingFamily {U : C} (R : Presieve U) where
  family : SemiRepresentableFamily.Over.{w} U
  generates : family.toPresieve = R

namespace GeneratingFamily

/-- The canonical, generally large, family indexed by all arrows of a presieve.  This is useful
as a fallback presentation; cardinal bounds should instead be recorded with a smaller chosen
generating family when one is available. -/
def ofUncurry {U : C} (R : Presieve U) : R.GeneratingFamily where
  family :=
    { index := R.uncurry
      obj := fun i ↦ CategoryTheory.Over.mk i.1.2 }
  generates := ofArrows_uncurry_eq R

end GeneratingFamily

/-- A presieve admits a generating family in the canonical site-index universe whose index type
has cardinality strictly below `κ`. -/
def hasGeneratingFamilyOfCardinalLT {U : C}
    (R : Presieve U) (κ : Cardinal.{w₂}) : Prop :=
  ∃ g : R.GeneratingFamily.{max u v}, HasCardinalLT g.family.index κ

end Presieve

end CategoryTheory
