/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Equality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic bicategorical equivalence calculus

This leaf owns operations intrinsic to one bicategorical equivalence: canonical
adjointification, reversal, and passage to the bicategory of adjunctions.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace Bicategory.Equivalence

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {x y : B}

/-- Canonically adjust a candidate unit so that it is compatible with a supplied invertible
counit. This is the unit-preserving counterpart to mathlib's `Bicategory.adjointifyCounit`,
obtained by applying that construction to the reversed pair. -/
@[stacks 0040 "adjointify the unit of bicategorical quasi-inverse data"]
def adjointifyUnit {f : x ⟶ y} {g : y ⟶ x}
    (η : 𝟙 x ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 y) :
    𝟙 x ≅ f ≫ g :=
  (Bicategory.adjointifyCounit ε.symm η.symm).symm

/-- The adjusted unit and the supplied counit satisfy the left triangle identity. -/
theorem adjointifyUnit.left_triangle {f : x ⟶ y} {g : y ⟶ x}
    (η : 𝟙 x ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 y) :
    leftZigzagIso (adjointifyUnit η ε) ε =
      λ_ f ≪≫ (ρ_ f).symm := sorry

/-- Construct a bicategorical equivalence from invertible comparison cells while retaining the
supplied counit and canonically adjusting the unit. -/
@[stacks 003L "equivalence from quasi-inverse data"]
def mkOfAdjointifyUnit {f : x ⟶ y} {g : y ⟶ x}
    (η : 𝟙 x ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 y) :
    x ≌ y where
  hom := f
  inv := g
  unit := adjointifyUnit η ε
  counit := ε
  left_triangle := adjointifyUnit.left_triangle η ε

/-- The forward `1`-morphism of `mkOfAdjointifyUnit` is the supplied forward morphism. -/
@[simp]
theorem mkOfAdjointifyUnit.hom {f : x ⟶ y} {g : y ⟶ x}
    (η : 𝟙 x ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 y) :
    (mkOfAdjointifyUnit η ε).hom = f := sorry

/-- The inverse `1`-morphism of `mkOfAdjointifyUnit` is the supplied inverse morphism. -/
@[simp]
theorem mkOfAdjointifyUnit.inv {f : x ⟶ y} {g : y ⟶ x}
    (η : 𝟙 x ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 y) :
    (mkOfAdjointifyUnit η ε).inv = g := sorry

/-- The unit of `mkOfAdjointifyUnit` is the canonical adjustment of the supplied candidate. -/
@[simp]
theorem mkOfAdjointifyUnit.unit {f : x ⟶ y} {g : y ⟶ x}
    (η : 𝟙 x ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 y) :
    (mkOfAdjointifyUnit η ε).unit = adjointifyUnit η ε := sorry

/-- The counit of `mkOfAdjointifyUnit` is the supplied counit. -/
@[simp]
theorem mkOfAdjointifyUnit.counit {f : x ⟶ y} {g : y ⟶ x}
    (η : 𝟙 x ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 y) :
    (mkOfAdjointifyUnit η ε).counit = ε := sorry

namespace Implementation

/-- The reversed unit and counit of an existing equivalence satisfy the required left triangle
identity. -/
private theorem symm.left_triangle (e : x ≌ y) :
    leftZigzagIso e.counit.symm e.unit.symm =
      λ_ e.inv ≪≫ (ρ_ e.inv).symm := sorry

end Implementation

/-- Reverse a bicategorical equivalence. The forward `1`-morphism is `e.inv`, and the original
counit and unit supply the reversed unit and counit. -/
@[stacks 0040 "reverse a bicategorical equivalence"]
def symm (e : x ≌ y) : y ≌ x where
  hom := e.inv
  inv := e.hom
  unit := e.counit.symm
  counit := e.unit.symm
  left_triangle := Implementation.symm.left_triangle e

/-- The forward `1`-morphism of the reversed equivalence is the original inverse. -/
@[simp]
theorem symm.hom (e : x ≌ y) :
    e.symm.hom = e.inv := sorry

/-- The inverse `1`-morphism of the reversed equivalence is the original forward morphism. -/
@[simp]
theorem symm.inv (e : x ≌ y) :
    e.symm.inv = e.hom := sorry

/-- The unit of the reversed equivalence is the inverse of the original counit. -/
@[simp]
theorem symm.unit (e : x ≌ y) :
    e.symm.unit = e.counit.symm := sorry

/-- The counit of the reversed equivalence is the inverse of the original unit. -/
@[simp]
theorem symm.counit (e : x ≌ y) :
    e.symm.counit = e.unit.symm := sorry

/-- The adjunction underlying a bicategorical equivalence. This forgets only that its unit and
counit are invertible; the `1`-morphisms and coherence cells are unchanged. -/
@[stacks 0040 "underlying adjunction of a bicategorical equivalence"]
def toAdjunction (e : x ≌ y) : e.hom ⊣ e.inv where
  unit := e.unit.hom
  counit := e.counit.hom
  left_triangle := e.left_triangle_hom
  right_triangle := e.right_triangle_hom

/-- Regard a bicategorical equivalence as a `1`-morphism in the bicategory of adjunctions.

This is the canonical comparison layer for pseudofunctoriality of equivalences: a general
pseudofunctor preserves identity and composition only up to invertible mate transformations,
which are precisely the `2`-isomorphisms of `Bicategory.Adj`. -/
@[stacks 0040 "adjunction-bicategory morphism of a bicategorical equivalence"]
def toAdjHom (e : x ≌ y) :
    Bicategory.Adj.mk x ⟶ Bicategory.Adj.mk y :=
  ⟨e.toAdjunction⟩

/-- The left adjoint underlying the `Adj`-morphism associated to an equivalence is its forward
`1`-morphism. -/
@[simp]
theorem toAdjHom.l (e : x ≌ y) :
    e.toAdjHom.l = e.hom := sorry

/-- The right adjoint underlying the `Adj`-morphism associated to an equivalence is its inverse
`1`-morphism. -/
@[simp]
theorem toAdjHom.r (e : x ≌ y) :
    e.toAdjHom.r = e.inv := sorry

/-- The adjunction carried by the `Adj`-morphism associated to an equivalence is the canonical
underlying adjunction. -/
@[simp]
theorem toAdjHom.adj (e : x ≌ y) :
    e.toAdjHom.adj = e.toAdjunction := sorry

/-- The identity equivalence becomes the identity `1`-morphism of the bicategory of
adjunctions. -/
@[simp]
theorem toAdjHom.id (x : B) :
    (Bicategory.Equivalence.id x).toAdjHom =
      𝟙 (Bicategory.Adj.mk x) := sorry

/-- The passage from an equivalence to its `Adj`-morphism is injective: the inverse cells of
the unit and counit are determined by their forward cells. -/
theorem toAdjHom.injective :
    Function.Injective (fun e : x ≌ y ↦ e.toAdjHom) := sorry

/-- Two bicategorical equivalences are equal exactly when their associated `Adj`-morphisms
are equal. -/
@[simp]
theorem toAdjHom.inj {e e' : x ≌ y} :
    e.toAdjHom = e'.toAdjHom ↔ e = e' := sorry

/-- The unit of the adjunction underlying an equivalence is the forward unit cell. -/
@[simp]
theorem toAdjunction.unit (e : x ≌ y) :
    e.toAdjunction.unit = e.unit.hom := sorry

/-- The counit of the adjunction underlying an equivalence is the forward counit cell. -/
@[simp]
theorem toAdjunction.counit (e : x ≌ y) :
    e.toAdjunction.counit = e.counit.hom := sorry

end Bicategory.Equivalence

end CategoryTheory
