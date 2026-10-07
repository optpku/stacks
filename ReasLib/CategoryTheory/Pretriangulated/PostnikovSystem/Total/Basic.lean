module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Basic

/-!
# Total Category of Finite Postnikov Systems

This leaf packages finite rows and Postnikov systems on them into a
Grothendieck-style total category. It owns the category structure and its
component laws. The forgetful functor to finite rows is developed in
`Total.Forget`.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The total space of finite Postnikov systems of length `n`: an object consists of a finite
row and a Postnikov system on that row. -/
@[stacks 0D7Z "total category of finite Postnikov systems"]
structure Total (D : Type u) [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
    (n : ℕ) where
  /-- The underlying finite row. -/
  base : ComposableArrows D n
  /-- The Postnikov system carried by the finite row. -/
  system : PostnikovSystem base

namespace Total

variable {n : ℕ}

/-- A morphism in the total category consists of a map of finite rows and a compatible
Postnikov-system morphism above it. -/
@[stacks 0D7Z "morphism in the total category of finite Postnikov systems"]
structure Hom (P Q : Total D n) where
  /-- The underlying morphism of finite rows. -/
  base : P.base ⟶ Q.base
  /-- The compatible morphism between the carried Postnikov systems. -/
  systemMap : PostnikovSystem.Morphism P.system Q.system base

namespace Hom

variable {P Q R : Total D n}

/-- The identity morphism of an object in the total category. -/
@[stacks 0D7Z]
def id (P : Total D n) : Hom P P where
  base := 𝟙 P.base
  systemMap := PostnikovSystem.Morphism.id P.system

/-- Composition of morphisms in the total category. -/
@[stacks 0D7Z]
def comp (f : Hom P Q) (g : Hom Q R) : Hom P R where
  base := f.base ≫ g.base
  systemMap := PostnikovSystem.Morphism.comp f.systemMap g.systemMap

/-- The base component of an identity total morphism is an identity. -/
@[simp]
theorem id_base (P : Total D n) : (id P).base = 𝟙 P.base := sorry

/-- The system component of an identity total morphism is the canonical identity system map. -/
@[simp]
theorem id_systemMap (P : Total D n) :
    (id P).systemMap = PostnikovSystem.Morphism.id P.system := sorry

/-- Base components of total morphisms compose in the base category. -/
@[simp]
theorem comp_base (f : Hom P Q) (g : Hom Q R) :
    (comp f g).base = f.base ≫ g.base := sorry

/-- System components of total morphisms compose over the composite base map. -/
@[simp]
theorem comp_systemMap (f : Hom P Q) (g : Hom Q R) :
    (comp f g).systemMap =
      PostnikovSystem.Morphism.comp f.systemMap g.systemMap := sorry

/-- Total morphisms are determined by their base maps and stagewise auxiliary maps. -/
@[ext (iff := false)]
theorem ext {f g : Hom P Q} (hbase : f.base = g.base)
    (hsystem : ∀ i, f.systemMap.yMap i = g.systemMap.yMap i) : f = g := sorry

/-- Two total morphisms agree exactly when their base maps and every auxiliary-object
component agree. -/
@[simp, stacks 0D7Z]
theorem ext_iff {f g : Hom P Q} :
    f = g ↔ f.base = g.base ∧ ∀ i, f.systemMap.yMap i = g.systemMap.yMap i := sorry

/-- The identity total morphism is a left identity for composition. -/
@[simp]
theorem id_comp (f : Hom P Q) : comp (id P) f = f := sorry

/-- The identity total morphism is a right identity for composition. -/
@[simp]
theorem comp_id (f : Hom P Q) : comp f (id Q) = f := sorry

/-- Composition of total morphisms is associative. -/
theorem comp_assoc {S : Total D n} (f : Hom P Q) (g : Hom Q R) (h : Hom R S) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- Finite Postnikov systems over varying finite rows form a category. -/
@[stacks 0D7Z "category of finite Postnikov systems"]
instance instCategory : Category (Total D n) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

/-- The base component of the categorical identity is an identity finite-row morphism. -/
@[simp]
theorem id_base (P : Total D n) : (𝟙 P : P ⟶ P).base = 𝟙 P.base := sorry

/-- The system component of the categorical identity is the identity Postnikov-system map. -/
@[simp]
theorem id_systemMap (P : Total D n) :
    (𝟙 P : P ⟶ P).systemMap = PostnikovSystem.Morphism.id P.system := sorry

/-- Base components of categorical composites compose in the category of finite rows. -/
@[simp]
theorem comp_base {P Q R : Total D n} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).base = f.base ≫ g.base := sorry

/-- System components of categorical composites are the composites of the system maps. -/
@[simp]
theorem comp_systemMap {P Q R : Total D n} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).systemMap =
      PostnikovSystem.Morphism.comp f.systemMap g.systemMap := sorry

/-- The auxiliary-object component of an identity total morphism is an identity. -/
@[simp, stacks 0D7Z "auxiliary evaluation of an identity"]
theorem id_yMap (P : Total D n) (i : Fin (n + 1)) :
    (𝟙 P : P ⟶ P).systemMap.yMap i = 𝟙 (P.system i) := sorry

/-- Auxiliary-object components of total morphisms compose pointwise. -/
@[simp, stacks 0D7Z "auxiliary evaluation of a composite"]
theorem comp_yMap {P Q R : Total D n} (f : P ⟶ Q) (g : Q ⟶ R)
    (i : Fin (n + 1)) :
    (f ≫ g).systemMap.yMap i = f.systemMap.yMap i ≫ g.systemMap.yMap i := sorry

end Total
end CategoryTheory.PostnikovSystem
