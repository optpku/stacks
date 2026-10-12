/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Over
public import ReasLib.CategoryTheory.Sites.Family

/-!
# Semi-representable families as formal coproducts

Semi-representable families are modeled by formal coproducts. Their fixed-target
form is a formal coproduct in a slice category, with a comparison to the indexed
families used for covering families.
-/

@[expose] public section

universe w v u v' u' v'' u''

namespace CategoryTheory

open CategoryTheory.Limits

namespace SemiRepresentableFamily

/-- Scoped notation for a semi-representable family, using mathlib's formal coproduct owner. -/
scoped notation "SR(" C ")" => _root_.CategoryTheory.Limits.FormalCoproduct C

end SemiRepresentableFamily

open scoped CategoryTheory.SemiRepresentableFamily

namespace SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- Applying a functor componentwise to a semi-representable family. -/
abbrev map {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    SR(C) ⥤ SR(D) :=
  FormalCoproduct.map F

/-- Componentwise mapping along the identity functor is the identity on semi-representable
families. -/
theorem map_id :
    map (𝟭 C) = 𝟭 (SR(C)) := sorry

/-- Componentwise mapping of semi-representable families commutes with composition of ambient
functors. -/
theorem map_comp {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) = map F ⋙ map G := sorry

/-- Componentwise mapping of a semi-representable family retains its source indexing type. -/
@[simp]
theorem map_obj_index {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (K : SR(C)) :
    ((map F).obj K).index = K.index := sorry

/-- Componentwise mapping applies a functor to every member of a semi-representable family. -/
@[simp]
theorem map_obj_obj {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (K : SR(C)) (i : K.index) :
    ((map F).obj K).obj i = F.obj (K.obj i) := sorry

/-- The reindexing function of a componentwise-mapped semi-representable-family morphism is
unchanged. -/
@[simp]
theorem map_map_f {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {K L : SR(C)} (φ : K ⟶ L) :
    ((map F).map φ).f = φ.f := sorry

/-- The components of a mapped semi-representable-family morphism are the images of the original
components. -/
@[simp]
theorem map_map_φ {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {K L : SR(C)} (φ : K ⟶ L) (i : K.index) :
    ((map F).map φ).φ i = F.map (φ.φ i) := sorry

/-- A semi-representable family over `X` is a formal coproduct in `C / X`. -/
@[stacks 01G0 "fixed-target semi-representable family"]
abbrev OverFamily (X : C) :=
  SR(CategoryTheory.Over X)

end SemiRepresentableFamily

namespace SemiRepresentableFamily

/-- Scoped notation for a semi-representable family with a fixed target. -/
scoped syntax "SR(" term ", " term ")" : term

scoped macro_rules
  | `(SR($C, $X)) => `(SemiRepresentableFamily.OverFamily (C := $C) $X)

end SemiRepresentableFamily

namespace SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

namespace OverFamily

/-- The singleton fixed-target family associated to one arrow `f : U ⟶ X`. -/
abbrev singleton {X U : C} (f : U ⟶ X) : SR(C, X) :=
  (FormalCoproduct.incl (CategoryTheory.Over X)).obj (CategoryTheory.Over.mk f)

/-- A singleton fixed-target family is indexed by `PUnit`. -/
@[simp]
theorem singleton_index {X U : C} (f : U ⟶ X) :
    (singleton f).index = PUnit := sorry

/-- The unique source of a singleton fixed-target family is the source of its defining arrow. -/
@[simp]
theorem singleton_obj_left {X U : C} (f : U ⟶ X) (i : (singleton f).index) :
    ((singleton f).obj i).left = U := sorry

/-- The unique structure map of a singleton fixed-target family is its defining arrow. -/
@[simp]
theorem singleton_obj_hom {X U : C} (f : U ⟶ X) (i : (singleton f).index) :
    ((singleton f).obj i).hom = f := sorry

/-- Build a fixed-target semi-representable family from an indexed family of arrows into `X`. -/
abbrev ofArrows {X : C} {I : Type w} (U : I → C) (π : ∀ i : I, U i ⟶ X) : SR(C, X) :=
  FormalCoproduct.ofArrows U π

/-- The index type of a fixed-target family built from arrows is the supplied indexing type. -/
@[simp]
theorem ofArrows_index {X : C} {I : Type w} (U : I → C) (π : ∀ i : I, U i ⟶ X) :
    (ofArrows U π).index = I := sorry

/-- The source object of an entry in a fixed-target family built from arrows is the supplied
source object. -/
@[simp]
theorem ofArrows_obj_left {X : C} {I : Type w} (U : I → C)
    (π : ∀ i : I, U i ⟶ X) (i : I) :
    ((ofArrows U π).obj i).left = U i := sorry

/-- The structure arrow of an entry in a fixed-target family built from arrows is the supplied
arrow. -/
@[simp]
theorem ofArrows_obj_hom {X : C} {I : Type w} (U : I → C)
    (π : ∀ i : I, U i ⟶ X) (i : I) :
    ((ofArrows U π).obj i).hom = π i := sorry

/-- Forgetting the structure maps to `X` sends a fixed-target semi-representable family to its
underlying semi-representable family. -/
abbrev forget {X : C} : SR(C, X) ⥤ SR(C) :=
  FormalCoproduct.forgetOver X

/-- The underlying family obtained by forgetting a fixed target retains its indexing type. -/
@[simp]
theorem forget_obj_index {X : C} (K : SR(C, X)) :
    (forget.obj K).index = K.index := sorry

/-- Forgetting the fixed target replaces each member by its underlying source object. -/
@[simp]
theorem forget_obj_obj {X : C} (K : SR(C, X)) (i : K.index) :
    (forget.obj K).obj i = (K.obj i).left := sorry

/-- Forgetting the fixed target preserves the reindexing function of a family morphism. -/
@[simp]
theorem forget_map_f {X : C} {K L : SR(C, X)} (φ : K ⟶ L) :
    (forget.map φ).f = φ.f := sorry

/-- Forgetting the fixed target replaces each slice component of a family morphism by its
underlying component in `C`. -/
@[simp]
theorem forget_map_φ {X : C} {K L : SR(C, X)} (φ : K ⟶ L) (i : K.index) :
    (forget.map φ).φ i = (φ.φ i).left := sorry

end OverFamily
end SemiRepresentableFamily

end CategoryTheory
