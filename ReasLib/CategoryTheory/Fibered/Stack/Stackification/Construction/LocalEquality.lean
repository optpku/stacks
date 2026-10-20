module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Lift
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Quotienting arrows by local equality

The separated category has the same objects as the original category.
Arrows are quotient classes of original arrows, and
Cartesian factorization descends the original input factor through the quotient.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory

noncomputable section

universe u v uX vX

namespace CategoryTheory.Functor.StackificationConstruction

variable {C : Type u} [Category.{v} C] {X : Type uX} [Category.{vX} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage)

private theorem equalitySieve_laws {a b : X} (f g : a ⟶ b) :
    ∀ {V W : C} (k : V ⟶ p.obj a),
      χ.cartesianHom k (⟨a, rfl⟩ : p.Fiber (p.obj a)) ≫ f =
        χ.cartesianHom k (⟨a, rfl⟩ : p.Fiber (p.obj a)) ≫ g →
      ∀ l : W ⟶ V,
        χ.cartesianHom (l ≫ k) (⟨a, rfl⟩ : p.Fiber (p.obj a)) ≫ f =
          χ.cartesianHom (l ≫ k) (⟨a, rfl⟩ : p.Fiber (p.obj a)) ≫ g := sorry

/-- Arrows on which two original total arrows become equal after the displayed
Cartesian restriction of their common source. -/
def equalitySieve {a b : X} (f g : a ⟶ b) : Sieve (p.obj a) where
  arrows _ k := χ.cartesianHom k (⟨a, rfl⟩ : p.Fiber (p.obj a)) ≫ f =
    χ.cartesianHom k (⟨a, rfl⟩ : p.Fiber (p.obj a)) ≫ g
  downward_closed := fun {_ _} {k} hk l ↦ equalitySieve_laws p χ f g k hk l

/-- The projected arrow is fixed, and equality holds on a covering sieve. -/
def LocallyEqual {a b : X} (f g : a ⟶ b) : Prop :=
  p.map f = p.map g ∧ equalitySieve p χ f g ∈ J (p.obj a)

/-- Local equality is an equivalence relation on parallel arrows. -/
theorem locallyEqual_equivalence (a b : X) :
    _root_.Equivalence (@LocallyEqual _ _ _ _ J p χ a b) := sorry

/-- Composition preserves local equality. -/
theorem locallyEqual_comp {a b c : X} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (hf : LocallyEqual J p χ f f') (hg : LocallyEqual J p χ g g') :
    LocallyEqual J p χ (f ≫ g) (f' ≫ g') := sorry

/-- The setoid identifying arrows that agree locally over the same base arrow. -/
def localSetoid (a b : X) : Setoid (a ⟶ b) where
  r := LocallyEqual J p χ
  iseqv := locallyEqual_equivalence J p χ a b

/-- The separated stage retains each original object as explicit data. -/
structure SeparatedData (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage) where
  /-- The underlying original object. -/
  obj : X

namespace SeparatedData

/-- Arrows are original arrows modulo local equality. -/
def Hom (a b : SeparatedData J p χ) := Quotient (localSetoid J p χ a.obj b.obj)

/-- The identity is the class of the original identity arrow. -/
def id (a : SeparatedData J p χ) : Hom J p χ a a := Quotient.mk'' (𝟙 a.obj)

/-- Composition is induced by composition of original representatives. -/
def comp {a b c : SeparatedData J p χ} (f : Hom J p χ a b) (g : Hom J p χ b c) :
    Hom J p χ a c :=
  Quotient.map₂ (fun f g ↦ f ≫ g) (fun _ _ h _ _ k ↦ locallyEqual_comp J p χ h k) f g

private theorem category_laws :
    (∀ (a b : SeparatedData J p χ) (f : Hom J p χ a b), comp J p χ (id J p χ a) f = f) ∧
    (∀ (a b : SeparatedData J p χ) (f : Hom J p χ a b), comp J p χ f (id J p χ b) = f) ∧
    (∀ (a b c d : SeparatedData J p χ) (f : Hom J p χ a b) (g : Hom J p χ b c)
      (h : Hom J p χ c d), comp J p χ (comp J p χ f g) h = comp J p χ f (comp J p χ g h)) := sorry

/-- The category on original objects with arrows modulo local equality. -/
@[reducible]
def category : Category.{vX} (SeparatedData J p χ) where
  Hom := Hom J p χ
  id := id J p χ
  comp := comp J p χ
  id_comp := fun f ↦ (category_laws J p χ).1 _ _ f
  comp_id := fun f ↦ (category_laws J p χ).2.1 _ _ f
  assoc := fun f g h ↦ (category_laws J p χ).2.2 _ _ _ _ f g h

end SeparatedData

/-- The bundled category of original objects and locally equal arrow classes. -/
def separatedCategory : Cat.{vX, uX} :=
  ⟨SeparatedData J p χ, SeparatedData.category J p χ⟩

/-- The carrier of the separated category. -/
abbrev Separated := (separatedCategory J p χ : Type uX)

namespace Separated

/-- The category supplied by the canonical separated bundle. -/
@[reducible]
def category : Category.{vX} (Separated J p χ) := Cat.str (separatedCategory J p χ)

private def projectionMap {a b : Separated J p χ} (f : a ⟶ b) : p.obj a.obj ⟶ p.obj b.obj :=
  Quotient.lift (fun (f : a.obj ⟶ b.obj) ↦ p.map f)
    (fun _ _ (h : LocallyEqual J p χ _ _) ↦ h.1) f

private theorem projection_laws :
    (∀ a : Separated J p χ, projectionMap J p χ (𝟙 a) = 𝟙 (p.obj a.obj)) ∧
    (∀ (a b c : Separated J p χ) (f : a ⟶ b) (g : b ⟶ c),
      projectionMap J p χ (f ≫ g) = projectionMap J p χ f ≫ projectionMap J p χ g) := sorry

/-- The base arrow is evaluated on an original representative; local equality
contains exactly the equality required to make this well defined. -/
def projection : Separated J p χ ⥤ C where
  obj a := p.obj a.obj
  map := projectionMap J p χ
  map_id := (projection_laws J p χ).1
  map_comp := fun f g ↦ (projection_laws J p χ).2 _ _ _ f g

/-- The original functor sends an arrow to its literal local-equality class. -/
def ofOriginal : X ⥤ Separated J p χ where
  obj a := ⟨a⟩
  map f := Quotient.mk'' f
  map_id := fun _ ↦ rfl
  map_comp := fun _ _ ↦ rfl

/-- A representative of a quotient arrow has the same displayed lift condition. -/
theorem representative_isHomLift {a b : Separated J p χ} {R S : C} (f : R ⟶ S)
    (τ : a ⟶ b) [(projection J p χ).IsHomLift f τ] : p.IsHomLift f (Quotient.out τ) := sorry

/-- Factor a quotient arrow through an original strongly Cartesian arrow,
using the original actual universal-property map on a quotient representative. -/
def factor {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] {c : Separated J p χ} (k : p.obj c.obj ⟶ R)
    (τ : c ⟶ (ofOriginal J p χ).obj b) [(projection J p χ).IsHomLift (k ≫ f) τ] :
    c ⟶ (ofOriginal J p χ).obj a := by
  let raw : c.obj ⟶ b := Quotient.out τ
  exact Quotient.mk'' (@Functor.IsStronglyCartesian.map C X _ _ p R S a b f φ
    inferInstance (p.obj c.obj) c.obj k (k ≫ f) rfl raw
    (representative_isHomLift J p χ (k ≫ f) τ))

private theorem mapIsStronglyCartesian_laws {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [hφ : p.IsStronglyCartesian f φ] :
    (projection J p χ).IsHomLift f ((ofOriginal J p χ).map φ) ∧
    ∀ (c : Separated J p χ) (k : p.obj c.obj ⟶ R)
      (τ : c ⟶ (ofOriginal J p χ).obj b) (hτ : (projection J p χ).IsHomLift (k ≫ f) τ),
      let value := @factor _ _ _ _ J p χ a b R S f φ hφ c k τ hτ
      ((projection J p χ).IsHomLift k value ∧ value ≫ (ofOriginal J p χ).map φ = τ) ∧
      ∀ r : c ⟶ (ofOriginal J p χ).obj a,
        (projection J p χ).IsHomLift k r ∧ r ≫ (ofOriginal J p χ).map φ = τ → r = value := sorry

/-- The class of an original strongly Cartesian arrow is strongly Cartesian. -/
theorem mapIsStronglyCartesian {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [hφ : p.IsStronglyCartesian f φ] :
    (projection J p χ).IsStronglyCartesian f ((ofOriginal J p χ).map φ) where
  toIsHomLift := (mapIsStronglyCartesian_laws J p χ f φ).1
  universal_property' := fun {c} k τ hτ ↦
    ⟨@factor _ _ _ _ J p χ a b R S f φ hφ c k τ hτ,
      (mapIsStronglyCartesian_laws J p χ f φ).2 c k τ hτ⟩

/-- The separated projection is fibered, with lifts induced by the original cleavage. -/
theorem isFibered : (projection J p χ).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  let l := χ.lift (x := a.obj) f
  exact ⟨⟨l.source⟩, Quotient.mk'' l.hom,
    @mapIsStronglyCartesian _ _ _ _ J p χ l.source a.obj R (p.obj a.obj) f l.hom l.isStronglyCartesian⟩

private theorem comparison_laws : ofOriginal J p χ ⋙ projection J p χ = p := sorry

/-- Local equality does not change the original strongly Cartesian source data. -/
def comparison : CartesianBasedFunctor p (projection J p χ) :=
  CartesianBasedFunctor.ofBasedFunctor
    { toFunctor := ofOriginal J p χ
      w := comparison_laws J p χ }
    (by
      intro a b φ hφ
      change (projection J p χ).IsStronglyCartesian
        ((projection J p χ).map ((ofOriginal J p χ).map φ)) ((ofOriginal J p χ).map φ)
      exact @mapIsStronglyCartesian _ _ _ _ J p χ a b (p.obj a) (p.obj b) (p.map φ) φ hφ)

end Separated

end CategoryTheory.Functor.StackificationConstruction
