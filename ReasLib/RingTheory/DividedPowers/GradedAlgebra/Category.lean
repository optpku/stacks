module

public import Mathlib.CategoryTheory.Functor.Basic
public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra.Hom
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra

/-!
# Nonnegative graded algebras with divided powers

This file bundles nonnegative graded algebras carrying divided powers, defines their
structure-preserving morphisms, and provides the category and its forgetful functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DirectSum

universe u v

namespace NonnegGradedAlgebra

variable {R : Type u} [CommRing R]
variable {A B C : NonnegGradedAlgebra.{u, v} R}

namespace DividedPowers

variable {gamma : NonnegGradedAlgebra.DividedPowers A}
variable {delta : NonnegGradedAlgebra.DividedPowers B}

/-- A homomorphism of strictly graded-commutative algebras with divided powers. -/
structure Hom (gamma : NonnegGradedAlgebra.DividedPowers A)
    (delta : NonnegGradedAlgebra.DividedPowers B) where
  /-- The underlying degree-preserving graded-algebra homomorphism. -/
  toGradedHom : A ⟶ B
  /-- Divided powers on the positive even part are preserved. -/
  map_gamma (n : ℕ) (x : A.evenPositivePart) :
    toGradedHom.evenMap (gamma n x) = delta n (toGradedHom.evenPositiveMap x)

namespace Hom

/-- A divided-power graded-algebra homomorphism acts degreewise on homogeneous elements. -/
instance : CoeFun (Hom gamma delta) (fun _ ↦ ∀ n : ℕ, A.piece n → B.piece n) where
  coe f n := f.toGradedHom.map n

/-- Degreewise evaluation is evaluation of the underlying graded-algebra homomorphism. -/
@[simp] theorem coe_apply (f : Hom gamma delta) (n : ℕ) (x : A.piece n) :
    f n x = f.toGradedHom.map n x := sorry

/-- The identity graded-algebra map preserves a divided-power structure. -/
theorem id_map_gamma (gamma : NonnegGradedAlgebra.DividedPowers A) (n : ℕ)
    (x : A.evenPositivePart) :
    (𝟙 A : A ⟶ A).evenMap (gamma n x) =
      gamma n ((𝟙 A : A ⟶ A).evenPositiveMap x) := sorry

/-- The identity homomorphism of a nonnegative graded algebra with divided powers. -/
def id (gamma : NonnegGradedAlgebra.DividedPowers A) : Hom gamma gamma where
  toGradedHom := 𝟙 A
  map_gamma := id_map_gamma gamma

/-- A composite of divided-power graded-algebra homomorphisms preserves divided powers. -/
theorem comp_map_gamma {C : NonnegGradedAlgebra.{u, v} R}
    {epsilon : NonnegGradedAlgebra.DividedPowers C}
    (g : Hom delta epsilon) (f : Hom gamma delta) (n : ℕ) (x : A.evenPositivePart) :
    (f.toGradedHom ≫ g.toGradedHom).evenMap (gamma n x) =
      epsilon n ((f.toGradedHom ≫ g.toGradedHom).evenPositiveMap x) := sorry

/-- Composition of divided-power graded-algebra homomorphisms. -/
def comp {C : NonnegGradedAlgebra.{u, v} R}
    {epsilon : NonnegGradedAlgebra.DividedPowers C}
    (g : Hom delta epsilon) (f : Hom gamma delta) : Hom gamma epsilon where
  toGradedHom := f.toGradedHom ≫ g.toGradedHom
  map_gamma := comp_map_gamma g f

/-- Divided-power graded-algebra homomorphisms are determined by their underlying graded maps. -/
theorem ext_toGradedHom {f g : Hom gamma delta}
    (h : f.toGradedHom = g.toGradedHom) : f = g := sorry

/-- Two divided-power graded-algebra homomorphisms are equal when their homogeneous maps agree. -/
@[ext] theorem ext {f g : Hom gamma delta}
    (h : ∀ n : ℕ, f.toGradedHom.map n = g.toGradedHom.map n) : f = g := sorry

/-- The identity divided-power homomorphism acts identically in each degree. -/
@[simp] theorem id_apply (gamma : NonnegGradedAlgebra.DividedPowers A)
    (n : ℕ) (x : A.piece n) : id gamma n x = x := sorry

/-- Composition of divided-power homomorphisms acts degreewise by composition. -/
@[simp] theorem comp_apply {C : NonnegGradedAlgebra.{u, v} R}
    {epsilon : NonnegGradedAlgebra.DividedPowers C}
    (g : Hom delta epsilon) (f : Hom gamma delta) (n : ℕ) (x : A.piece n) :
    comp g f n x = g n (f n x) := sorry

/-- Composing with the identity on the source leaves a divided-power graded map unchanged. -/
@[simp] theorem id_comp (f : Hom gamma delta) : comp f (id gamma) = f := sorry

/-- Composing with the identity on the target leaves a divided-power graded map unchanged. -/
@[simp] theorem comp_id (f : Hom gamma delta) : comp (id delta) f = f := sorry

/-- Composition of divided-power graded-algebra homomorphisms is associative. -/
theorem assoc {C D : NonnegGradedAlgebra.{u, v} R}
    {epsilon : NonnegGradedAlgebra.DividedPowers C}
    {zeta : NonnegGradedAlgebra.DividedPowers D}
    (f : Hom gamma delta) (g : Hom delta epsilon) (h : Hom epsilon zeta) :
    comp h (comp g f) = comp (comp h g) f := sorry

/-- The underlying graded map of the identity divided-power map is the identity. -/
@[simp] theorem toGradedHom_id (gamma : NonnegGradedAlgebra.DividedPowers A) :
    (id gamma).toGradedHom = 𝟙 A := sorry

/-- The underlying graded map of a composite is the composite of the underlying maps. -/
@[simp] theorem toGradedHom_comp {C : NonnegGradedAlgebra.{u, v} R}
    {epsilon : NonnegGradedAlgebra.DividedPowers C}
    (f : Hom gamma delta) (g : Hom delta epsilon) :
    (comp g f).toGradedHom = f.toGradedHom ≫ g.toGradedHom := sorry

end Hom

end DividedPowers

end NonnegGradedAlgebra

/-- A nonnegative graded algebra bundled with a divided-power structure. -/
@[stacks 09PG "bundled graded divided-power algebra"]
structure DividedPowerGradedAlgebra (R : Type u) [CommRing R] where
  /-- The underlying nonnegative graded algebra. -/
  toGradedAlgebra : NonnegGradedAlgebra.{u, v} R
  /-- The divided powers on the positive even part. -/
  gamma : NonnegGradedAlgebra.DividedPowers toGradedAlgebra

namespace DividedPowerGradedAlgebra

variable {R : Type u} [CommRing R]

/-- Bundle a nonnegative graded algebra with its chosen divided-power structure. -/
def of (A : NonnegGradedAlgebra.{u, v} R)
    (gamma : NonnegGradedAlgebra.DividedPowers A) :
    DividedPowerGradedAlgebra.{u, v} R where
  toGradedAlgebra := A
  gamma := gamma

end DividedPowerGradedAlgebra

/-- Nonnegative graded algebras with divided powers form a category. -/
instance {R : Type u} [CommRing R] :
    Category (DividedPowerGradedAlgebra.{u, v} R) where
  Hom A B := NonnegGradedAlgebra.DividedPowers.Hom A.gamma B.gamma
  id A := NonnegGradedAlgebra.DividedPowers.Hom.id A.gamma
  comp f g := NonnegGradedAlgebra.DividedPowers.Hom.comp g f
  id_comp := NonnegGradedAlgebra.DividedPowers.Hom.id_comp
  comp_id := NonnegGradedAlgebra.DividedPowers.Hom.comp_id
  assoc := NonnegGradedAlgebra.DividedPowers.Hom.assoc

namespace DividedPowerGradedAlgebra

namespace Implementation

/-- The underlying graded map of a categorical identity is the graded identity. -/
theorem forgetMapId {R : Type u} [CommRing R]
    (A : DividedPowerGradedAlgebra.{u, v} R) :
    (𝟙 A : A ⟶ A).toGradedHom = 𝟙 A.toGradedAlgebra := sorry

/-- The underlying graded map of a categorical composite is the composite of underlying maps. -/
theorem forgetMapComp {R : Type u} [CommRing R]
    {A B C : DividedPowerGradedAlgebra.{u, v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toGradedHom = f.toGradedHom ≫ g.toGradedHom := sorry

end Implementation

/-- Forget the divided powers on a nonnegative graded algebra. -/
def forget (R : Type u) [CommRing R] :
    DividedPowerGradedAlgebra.{u, v} R ⥤ NonnegGradedAlgebra.{u, v} R where
  obj A := A.toGradedAlgebra
  map f := f.toGradedHom
  map_id := Implementation.forgetMapId
  map_comp := Implementation.forgetMapComp

/-- The forgetful functor sends a divided-power graded algebra to its underlying graded
algebra. -/
@[simp] theorem forget_obj {R : Type u} [CommRing R]
    (A : DividedPowerGradedAlgebra.{u, v} R) :
    (forget R).obj A = A.toGradedAlgebra := sorry

/-- The forgetful functor sends a divided-power morphism to its underlying graded map. -/
@[simp] theorem forget_map {R : Type u} [CommRing R]
    {A B : DividedPowerGradedAlgebra.{u, v} R} (f : A ⟶ B) :
    (forget R).map f = f.toGradedHom := sorry

end DividedPowerGradedAlgebra

#synth Category (DividedPowerGradedAlgebra.{0, 0} ℤ)
