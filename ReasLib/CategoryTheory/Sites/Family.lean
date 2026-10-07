module

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

/-- An indexed family of arrows in `C` with a fixed common target `U`. -/
@[stacks 0396 "fixed-target indexed family",
  stacks 01G0 "semi-representable family over an object"]
structure Over (U : C) where
  index : Type w
  obj : index → CategoryTheory.Over U

namespace Over

/-- A reindexing map between fixed-target families, together with component maps in `C / U`. -/
@[stacks 00VT "morphism of fixed-target families",
  stacks 01G0 "morphism of semi-representable families over an object"]
structure Hom {U : C} (𝒰 : SemiRepresentableFamily.Over.{w₁} U)
    (𝒱 : SemiRepresentableFamily.Over.{w₂} U) where
  α : 𝒰.index → 𝒱.index
  f : ∀ i : 𝒰.index, 𝒰.obj i ⟶ 𝒱.obj (α i)

/-- The identity componentwise reindexing of a fixed-target family. -/
@[stacks 00VT "identity morphism of fixed-target families"]
def Hom.id (𝒰 : SemiRepresentableFamily.Over.{w} U) : Hom 𝒰 𝒰 where
  α := fun i ↦ i
  f := fun i ↦ 𝟙 (𝒰.obj i)

/-- Compose componentwise reindexings whose index types may lie in different universes. -/
@[stacks 00VT "composition of fixed-target family morphisms"]
def Hom.comp {𝒰 : SemiRepresentableFamily.Over.{w₁} U}
    {𝒱 : SemiRepresentableFamily.Over.{w₂} U}
    {𝒲 : SemiRepresentableFamily.Over.{w₃} U}
    (φ : Hom 𝒰 𝒱) (ψ : Hom 𝒱 𝒲) : Hom 𝒰 𝒲 where
  α := fun i ↦ ψ.α (φ.α i)
  f := fun i ↦ φ.f i ≫ ψ.f (φ.α i)

/-- Fixed-target families form the expected quiver of componentwise refinement maps. -/
@[stacks 01G0 "quiver of semi-representable families over an object"]
instance instQuiver {U : C} : Quiver (SemiRepresentableFamily.Over.{w} U) where
  Hom 𝒰 𝒱 := Hom 𝒰 𝒱

/-- Fixed-target families form the category whose morphisms reindex the family and
provide a slice morphism at every component. -/
@[stacks 01G0 "category of semi-representable families over an object"]
instance instCategory {U : C} : Category (SemiRepresentableFamily.Over.{w} U) where
  Hom 𝒰 𝒱 := Hom 𝒰 𝒱
  id 𝒰 := Hom.id 𝒰
  comp φ ψ := Hom.comp φ ψ
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The underlying component of a composite family morphism is the composite of the underlying
component morphisms. -/
@[simp, stacks 01G0 "composition readout for family morphisms"]
theorem Hom.comp_left {U : C} {𝒰 𝒱 𝒲 : SemiRepresentableFamily.Over.{w} U}
    (φ : 𝒰 ⟶ 𝒱) (ψ : 𝒱 ⟶ 𝒲) (i : 𝒰.index) :
    ((φ ≫ ψ).f i).left = (φ.f i).left ≫ (ψ.f (φ.α i)).left := sorry

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
    ((singleton f).obj i).left = V := sorry

/-- The structure map of the unique member of a singleton family is its defining arrow. -/
@[simp, stacks 0396 "singleton-family arrow readout"]
theorem singleton_obj_hom {V : C} (f : V ⟶ U) (i : (singleton f).index) :
    ((singleton f).obj i).hom = f := sorry

/-- A family built from arrows has the corresponding slice object at each index. -/
@[simp, stacks 0396 "explicit-family object readout"]
theorem ofArrows_obj {I : Type w₁} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) (i : I) :
    (ofArrows Uᵢ π).obj i = CategoryTheory.Over.mk (π i) := sorry

/-- The source of a member of a family built from arrows is its specified source. -/
@[simp, stacks 0396 "explicit-family source readout"]
theorem ofArrows_obj_left {I : Type w₁} (Uᵢ : I → C)
    (π : ∀ i : I, Uᵢ i ⟶ U) (i : I) :
    ((ofArrows Uᵢ π).obj i).left = Uᵢ i := sorry

/-- The structure map of a member of a family built from arrows is the specified arrow. -/
@[simp, stacks 0396 "explicit-family arrow readout"]
theorem ofArrows_obj_hom {I : Type w₁} (Uᵢ : I → C)
    (π : ∀ i : I, Uᵢ i ⟶ U) (i : I) :
    ((ofArrows Uᵢ π).obj i).hom = π i := sorry

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
    ((𝒰.bind 𝒱).obj ij).left = ((𝒱 ij.1).obj ij.2).left := sorry

/-- The arrow of a member of `𝒰.bind 𝒱` is the corresponding composite arrow. -/
@[simp, stacks 0396 "composed-family arrow readout"]
theorem bind_obj_hom (𝒰 : SemiRepresentableFamily.Over.{w₁} U)
    (𝒱 : ∀ i : 𝒰.index, SemiRepresentableFamily.Over.{w₂} (𝒰.obj i).left)
    (ij : (𝒰.bind 𝒱).index) :
    ((𝒰.bind 𝒱).obj ij).hom =
      ((𝒱 ij.1).obj ij.2).hom ≫ (𝒰.obj ij.1).hom := sorry

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
    (map F 𝒰).obj i = F.obj (𝒰.obj i) := sorry

/-- The structure map of a componentwise-mapped family is the structure map of the corresponding
image in the target slice category. -/
@[simp]
theorem map_obj_hom {U V : C}
    (F : CategoryTheory.Over U ⥤ CategoryTheory.Over V)
    (𝒰 : SemiRepresentableFamily.Over.{w₁} U) (i : 𝒰.index) :
    ((map F 𝒰).obj i).hom = (F.obj (𝒰.obj i)).hom := sorry

/-- A morphism from a base-changed family has component maps compatible with the base map. -/
@[stacks 00VT "family-morphism base compatibility"]
theorem Hom.map_hom {U V : C}
    {𝒰 : SemiRepresentableFamily.Over.{w₁} U}
    {𝒱 : SemiRepresentableFamily.Over.{w₂} V}
    (base : U ⟶ V)
    (φ : Hom (SemiRepresentableFamily.Over.map (CategoryTheory.Over.map base) 𝒰) 𝒱)
    (i : 𝒰.index) :
    (φ.f i).left ≫ (𝒱.obj (φ.α i)).hom = (𝒰.obj i).hom ≫ base := sorry

/-- The component maps of a morphism between families over the same target commute with the
structure maps, written in the identity-base form used by pullback constructions. -/
@[stacks 00VT "same-target family-morphism compatibility"]
theorem Hom.map_hom_id {U : C}
    {𝒰 : SemiRepresentableFamily.Over.{w₁} U}
    {𝒱 : SemiRepresentableFamily.Over.{w₂} U}
    (φ : Hom 𝒰 𝒱) (i : 𝒰.index) :
    (φ.f i).left ≫ (𝒱.obj (φ.α i)).hom = (𝒰.obj i).hom ≫ 𝟙 U := sorry

/-- The presieve generated by a fixed-target indexed family. -/
abbrev toPresieve (𝒰 : Over.{w} U) : Presieve U :=
  Presieve.ofArrows (fun i ↦ (𝒰.obj i).left) fun i ↦ (𝒰.obj i).hom

/-- Pairwise pullbacks for the presieve generated by a family are available componentwise to
typeclass search. -/
instance pairwiseHasPullback (𝒰 : Over.{w} U)
    [𝒰.toPresieve.HasPairwisePullbacks] (i j : 𝒰.index) :
    Limits.HasPullback (𝒰.obj i).hom (𝒰.obj j).hom := sorry

/-- The presieve view of a family built from explicit arrows is the original presieve. -/
@[simp]
theorem toPresieve_ofArrows {I : Type w₁} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) :
    toPresieve (ofArrows Uᵢ π) = Presieve.ofArrows Uᵢ π := sorry

/-- Reindexing an explicit family along `ULift.down` does not change its generated presieve. -/
@[simp]
theorem toPresieve_ofArrows_ulift {I : Type w₁} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) :
    toPresieve (ofArrows (fun i : ULift.{w₂} I ↦ Uᵢ i.down) fun i ↦ π i.down) =
      Presieve.ofArrows Uᵢ π := sorry

/-- The sieve generated by a fixed-target indexed family. -/
@[stacks 00Z1 "sieve generated by a fixed-target family"]
abbrev toSieve (𝒰 : Over.{w} U) : Sieve U :=
  Sieve.generate (toPresieve 𝒰)

/-- The sieve view of a family built from explicit arrows is the original generated sieve. -/
@[simp, stacks 00Z1 "explicit-family sieve readout"]
theorem toSieve_ofArrows {I : Type w₁} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) :
    toSieve (ofArrows Uᵢ π) = Sieve.ofArrows Uᵢ π := sorry

/-- Reindexing an explicit family along `ULift.down` does not change its generated sieve. -/
@[simp, stacks 00Z1 "lifted explicit-family sieve readout"]
theorem toSieve_ofArrows_ulift {I : Type w₁} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) :
    toSieve (ofArrows (fun i : ULift.{w₂} I ↦ Uᵢ i.down) fun i ↦ π i.down) =
      Sieve.ofArrows Uᵢ π := sorry

end Over
end SemiRepresentableFamily

namespace Presieve

/-- The family indexed by all arrows in a presieve generates that presieve. -/
theorem ofArrows_uncurry_eq {U : C} (R : Presieve U) :
    Presieve.ofArrows
      (fun i : R.uncurry ↦ (CategoryTheory.Over.mk i.1.2).left)
      (fun i ↦ (CategoryTheory.Over.mk i.1.2).hom) = R := sorry

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
