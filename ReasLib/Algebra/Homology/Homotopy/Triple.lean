/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Endpoint triples for homotopies

This leaf packages the elementary functorial data carried by a pair of maps of homological
complexes together with a homotopy between them.  It deliberately does not assume a particular
complex shape or use a cylinder construction.
-/

open CategoryTheory

universe w v u

namespace HomologicalComplex

variable {ι : Type w} {C : Type u} [Category.{v} C] [Preadditive C]
variable {c : ComplexShape ι}
variable {A B D E : HomologicalComplex C c}

/-- A pair of maps of homological complexes together with a homotopy between the two maps. -/
@[ext, stacks 01A2 "endpoint maps equipped with a chain homotopy"]
structure HomotopyTriple (A B : HomologicalComplex C c) where
  left : A ⟶ B
  right : A ⟶ B
  homotopy : Homotopy left right

namespace HomotopyTriple

/-- Two homotopy triples are equal when their endpoints and homotopy components agree. -/
theorem ext_of_hom
    {left₁ right₁ left₂ right₂ : A ⟶ B}
    {homotopy₁ : Homotopy left₁ right₁} {homotopy₂ : Homotopy left₂ right₂}
    (hleft : left₁ = left₂) (hright : right₁ = right₂)
    (hhomotopy : homotopy₁.hom = homotopy₂.hom) :
    (HomotopyTriple.mk left₁ right₁ homotopy₁ : HomotopyTriple A B) =
      HomotopyTriple.mk left₂ right₂ homotopy₂ := sorry

/-- Postcomposition of both endpoints and their connecting homotopy. -/
@[stacks 01A2 "postcomposition of homotopy triples"]
def postcomp (g : B ⟶ D) : HomotopyTriple A B → HomotopyTriple A D
  | ⟨left, right, homotopy⟩ =>
      { left := left ≫ g
        right := right ≫ g
        homotopy := homotopy.compRight g }

/-- The morphism in `Type` induced by postcomposition of homotopy triples. -/
@[stacks 01A2 "postcomposition map of homotopy triples"]
def postcompMap (g : B ⟶ D) : HomotopyTriple A B ⟶ HomotopyTriple A D :=
  TypeCat.ofHom (postcomp g)

/-- Precomposition of both endpoints and their connecting homotopy. -/
@[stacks 01A2 "precomposition of homotopy triples"]
def precomp (f : A ⟶ B) : HomotopyTriple B D → HomotopyTriple A D
  | ⟨left, right, homotopy⟩ =>
      { left := f ≫ left
        right := f ≫ right
        homotopy := homotopy.compLeft f }

/-- The morphism in `Type` induced by precomposition of homotopy triples. -/
@[stacks 01A2 "precomposition map of homotopy triples"]
def precompMap (f : A ⟶ B) : HomotopyTriple B D ⟶ HomotopyTriple A D :=
  TypeCat.ofHom (precomp f)

/-- The left endpoint of a postcomposed homotopy triple. -/
@[simp]
theorem postcomp_left (g : B ⟶ D) (x : HomotopyTriple A B) :
    (postcomp g x).left = x.left ≫ g := sorry

/-- The right endpoint of a postcomposed homotopy triple. -/
@[simp]
theorem postcomp_right (g : B ⟶ D) (x : HomotopyTriple A B) :
    (postcomp g x).right = x.right ≫ g := sorry

/-- The homotopy in a postcomposed homotopy triple. -/
@[simp]
theorem postcomp_homotopy (g : B ⟶ D) (x : HomotopyTriple A B) :
    (postcomp g x).homotopy = x.homotopy.compRight g := sorry

/-- The left endpoint of a precomposed homotopy triple. -/
@[simp]
theorem precomp_left (f : A ⟶ B) (x : HomotopyTriple B D) :
    (precomp f x).left = f ≫ x.left := sorry

/-- The right endpoint of a precomposed homotopy triple. -/
@[simp]
theorem precomp_right (f : A ⟶ B) (x : HomotopyTriple B D) :
    (precomp f x).right = f ≫ x.right := sorry

/-- The homotopy in a precomposed homotopy triple. -/
@[simp]
theorem precomp_homotopy (f : A ⟶ B) (x : HomotopyTriple B D) :
    (precomp f x).homotopy = x.homotopy.compLeft f := sorry

/-- Postcomposition by an identity map fixes a homotopy triple. -/
theorem postcomp_id (x : HomotopyTriple A B) :
    postcomp (𝟙 B) x = x := sorry

/-- Postcomposition of homotopy triples respects composition. -/
theorem postcomp_comp (f : B ⟶ D) (g : D ⟶ E) (x : HomotopyTriple A B) :
    postcomp (f ≫ g) x = postcomp g (postcomp f x) := sorry

/-- The `Type` morphism induced by postcomposition with an identity is the identity. -/
theorem postcompMap_id :
    postcompMap (A := A) (𝟙 B) = 𝟙 (HomotopyTriple A B) := sorry

/-- The `Type` morphisms induced by postcomposition respect composition. -/
theorem postcompMap_comp (f : B ⟶ D) (g : D ⟶ E) :
    postcompMap (A := A) (f ≫ g) = postcompMap (A := A) f ≫ postcompMap (A := A) g := sorry

/-- The `Type` morphism induced by precomposition with an identity is the identity. -/
theorem precompMap_id :
    precompMap (D := D) (𝟙 A) = 𝟙 (HomotopyTriple A D) := sorry

/-- The `Type` morphisms induced by precomposition respect composition contravariantly. -/
theorem precompMap_comp (f : A ⟶ B) (g : B ⟶ D) :
    precompMap (D := E) (f ≫ g) =
      precompMap (D := E) g ≫ precompMap (D := E) f := sorry

/-- Precomposition by an identity map fixes a homotopy triple. -/
theorem precomp_id (x : HomotopyTriple A D) :
    precomp (𝟙 A) x = x := sorry

/-- Precomposition of homotopy triples respects composition. -/
theorem precomp_comp (f : A ⟶ B) (g : B ⟶ D) (x : HomotopyTriple D E) :
    precomp (f ≫ g) x = precomp f (precomp g x) := sorry

/-- Precomposition and postcomposition of a homotopy triple commute. -/
theorem postcomp_precomp (f : A ⟶ B) (g : D ⟶ E) (x : HomotopyTriple B D) :
    postcomp g (precomp f x) = precomp f (postcomp g x) := sorry

/-- The covariant functor sending a target complex to endpoint maps from `A` with a homotopy
between them. -/
@[stacks 01A2 "target functor of homotopy triples"]
def functor (A : HomologicalComplex C c) :
    HomologicalComplex C c ⥤ Type (max v w) where
  obj B := HomotopyTriple A B
  map f := HomotopyTriple.postcompMap (A := A) f
  map_id _ := HomotopyTriple.postcompMap_id
  map_comp f g := HomotopyTriple.postcompMap_comp (A := A) f g

/-- The action of the homotopy-triple functor is endpoint postcomposition. -/
@[simp]
theorem functor_map_apply (g : B ⟶ D) (x : HomotopyTriple A B) :
    (functor A).map g x = postcomp g x := sorry

/-- Source precomposition is natural in the target homological complex. -/
theorem precompMap_naturality (f : A ⟶ B) (g : D ⟶ E) :
    (functor B).map g ≫ precompMap (D := E) f =
      precompMap (D := D) f ≫ (functor A).map g := sorry

/-- Precomposition by a complex morphism as a natural transformation between homotopy-triple
functors. -/
@[stacks 01A2 "precomposition natural transformation of homotopy triples"]
def precompNatTrans (f : A ⟶ B) : functor B ⟶ functor A where
  app D := precompMap (D := D) f
  naturality _ _ g := precompMap_naturality f g

/-- The component of the precomposition natural transformation is the precomposition map. -/
@[simp]
theorem precompNatTrans_app (f : A ⟶ B) (D : HomologicalComplex C c) :
    (precompNatTrans f).app D = precompMap (D := D) f := sorry

end HomotopyTriple

end HomologicalComplex
