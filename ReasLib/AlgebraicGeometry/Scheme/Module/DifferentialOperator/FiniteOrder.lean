/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialOperator.FiniteOrder
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

/-!
# Finite-order differential operators between quasicoherent modules

For a scheme morphism `X ⟶ S`, quasicoherent modules on `X` form an additive category whose
morphisms are differential operators of arbitrary finite order relative to `S`.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- Quasicoherent modules on `X`, regarded as objects of the category with finite-order
differential operators relative to `a : X ⟶ S`. -/
def FiniteOrderDifferentialOperatorCat (a : X ⟶ S) : Type (u + 1) := Scheme.QCoh X

namespace FiniteOrderDifferentialOperatorCat

variable (a : X ⟶ S)

/-- The equivalence between objects of the finite-order category and quasicoherent modules. -/
def qcohEquiv : FiniteOrderDifferentialOperatorCat a ≃ Scheme.QCoh X := Equiv.refl _

attribute [irreducible] FiniteOrderDifferentialOperatorCat

/-- Regard a quasicoherent module as an object of the finite-order category. -/
def ofQCoh (F : Scheme.QCoh X) : FiniteOrderDifferentialOperatorCat a :=
  (qcohEquiv a).symm F

/-- The quasicoherent module represented by an object of the finite-order category. -/
def asQCoh (F : FiniteOrderDifferentialOperatorCat a) : Scheme.QCoh X :=
  qcohEquiv a F

/-- Passing a quasicoherent module into the finite-order category and back recovers it. -/
@[simp]
theorem asQCoh_ofQCoh (F : Scheme.QCoh X) : asQCoh a (ofQCoh a F) = F :=
  (qcohEquiv a).apply_symm_apply F

/-- The module sheaf underlying an object of the finite-order category. -/
abbrev underlying (F : FiniteOrderDifferentialOperatorCat a) : X.Modules :=
  Scheme.QCoh.inclusion X |>.obj (asQCoh a F)

/-- The module underlying an object constructed from a quasicoherent module is its object. -/
@[simp]
theorem underlying_ofQCoh (F : Scheme.QCoh X) : underlying a (ofQCoh a F) = F.obj := by
  change (asQCoh a (ofQCoh a F)).obj = F.obj
  rw [asQCoh_ofQCoh]

/-- The coefficient-sheaf morphism defining differential operators relative to `a`. -/
abbrev coefficientMap :=
  RingedSpace.Hom.inverseImageStructureSheafHomComm a.toShHom

/-- Finite-order differential operators between two quasicoherent modules. -/
abbrev Hom (F G : FiniteOrderDifferentialOperatorCat a) :=
  DifferentialOperators.FiniteOrder
    (J := Opens.grothendieckTopology X)
    (coefficientMap (X := X) (S := S) a)
    (underlying (X := X) (S := S) a F)
    (underlying (X := X) (S := S) a G)

/-- The identity finite-order differential operator. -/
def id (F : FiniteOrderDifferentialOperatorCat a) : Hom a F F :=
  DifferentialOperators.FiniteOrder.id
    (coefficientMap (X := X) (S := S) a)
    (underlying (X := X) (S := S) a F)

/-- Composition of finite-order differential operators. -/
def comp {F G H : FiniteOrderDifferentialOperatorCat a}
    (D : Hom a F G) (E : Hom a G H) : Hom a F H :=
  DifferentialOperators.FiniteOrder.comp
    (φ := coefficientMap (X := X) (S := S) a)
    (F := underlying (X := X) (S := S) a F)
    (G := underlying (X := X) (S := S) a G)
    (H := underlying (X := X) (S := S) a H) D E

/-- The restricted-scalar morphism underlying a morphism in the finite-order category. -/
abbrev toHom {F G : FiniteOrderDifferentialOperatorCat a} (D : Hom a F G) :
    (restrictionAlong (coefficientMap (X := X) (S := S) a)).obj
        (underlying (X := X) (S := S) a F) ⟶
      (restrictionAlong (coefficientMap (X := X) (S := S) a)).obj
        (underlying (X := X) (S := S) a G) :=
  DifferentialOperators.FiniteOrder.toHom
    (φ := coefficientMap (X := X) (S := S) a)
    (F := underlying (X := X) (S := S) a F)
    (G := underlying (X := X) (S := S) a G) D

/-- The underlying morphism of the identity is the identity. -/
@[simp]
theorem toHom_id (F : FiniteOrderDifferentialOperatorCat a) :
    toHom a (id a F) =
      𝟙 ((restrictionAlong (coefficientMap (X := X) (S := S) a)).obj
        (underlying (X := X) (S := S) a F)) :=
  rfl

/-- The underlying morphism of a composite is the composite of the underlying morphisms. -/
@[simp]
theorem toHom_comp {F G H : FiniteOrderDifferentialOperatorCat a}
    (D : Hom a F G) (E : Hom a G H) :
    toHom a (comp a D E) = toHom a D ≫ toHom a E :=
  rfl

/-- Finite-order differential operators give the quasicoherent modules on `X` a category
structure. -/
instance instCategory : Category (FiniteOrderDifferentialOperatorCat a) where
  Hom := Hom a
  id := id a
  comp := comp a
  id_comp := by sorry
  comp_id := by
    intro F G D
    apply DifferentialOperators.FiniteOrder.ext
    simp
  assoc := by
    intro F G H I D E K
    apply DifferentialOperators.FiniteOrder.ext
    simp

/-- A categorical morphism has an explicit restricted-scalar underlying morphism. -/
abbrev homToHom {F G : FiniteOrderDifferentialOperatorCat a} (D : F ⟶ G) :
    (restrictionAlong (coefficientMap (X := X) (S := S) a)).obj
        (underlying (X := X) (S := S) a F) ⟶
      (restrictionAlong (coefficientMap (X := X) (S := S) a)).obj
        (underlying (X := X) (S := S) a G) :=
  toHom a D

/-- Categorical identity has the identity restricted-scalar underlying morphism. -/
@[simp]
theorem homToHom_id (F : FiniteOrderDifferentialOperatorCat a) :
    homToHom a (𝟙 F) =
      𝟙 ((restrictionAlong (coefficientMap (X := X) (S := S) a)).obj
        (underlying (X := X) (S := S) a F)) :=
  rfl

/-- Categorical composition is ordinary composition on restricted-scalar underlying morphisms. -/
@[simp]
theorem homToHom_comp {F G H : FiniteOrderDifferentialOperatorCat a}
    (D : F ⟶ G) (E : G ⟶ H) :
    homToHom a (D ≫ E) = homToHom a D ≫ homToHom a E :=
  rfl

/-- Transport a finite-order morphism along equalities identifying its underlying source and
target modules. -/
def transport {F G : FiniteOrderDifferentialOperatorCat a} {M N : X.Modules}
    (hF : underlying a F = M) (hG : underlying a G = N) (D : Hom a F G) :
    DifferentialOperators.FiniteOrder
      (J := Opens.grothendieckTopology X) (coefficientMap a) M N := by
  subst M
  subst N
  exact D

/-- The finite-order differential-operator category is preadditive. -/
instance instPreadditive : Preadditive (FiniteOrderDifferentialOperatorCat a) where
  homGroup := fun F G ↦ inferInstanceAs (AddCommGroup (Hom a F G))
  comp_add := by sorry
  add_comp := by
    intro F G H D E K
    apply DifferentialOperators.FiniteOrder.ext
    change
      (homToHom (X := X) (S := S) a (F := F) (G := G) D +
        homToHom (X := X) (S := S) a (F := F) (G := G) E) ≫
          homToHom (X := X) (S := S) a (F := G) (G := H) K =
        homToHom (X := X) (S := S) a (F := F) (G := G) D ≫
            homToHom (X := X) (S := S) a (F := G) (G := H) K +
          homToHom (X := X) (S := S) a (F := F) (G := G) E ≫
            homToHom (X := X) (S := S) a (F := G) (G := H) K
    exact Preadditive.add_comp _ _ _
      (homToHom (X := X) (S := S) a (F := F) (G := G) D)
      (homToHom (X := X) (S := S) a (F := F) (G := G) E)
      (homToHom (X := X) (S := S) a (F := G) (G := H) K)

/-- The finite-order differential-operator category admits all finite biproducts. -/
instance instHasFiniteBiproducts :
    CategoryTheory.Limits.HasFiniteBiproducts (FiniteOrderDifferentialOperatorCat a) := by
  sorry

/-- Forgetting a zero morphism gives the zero restricted-scalar morphism. -/
@[simp]
theorem homToHom_zero {F G : FiniteOrderDifferentialOperatorCat a} :
    homToHom a (0 : F ⟶ G) = 0 :=
  rfl

/-- Forgetting a sum of morphisms gives the sum of their restricted-scalar morphisms. -/
@[simp]
theorem homToHom_add {F G : FiniteOrderDifferentialOperatorCat a} (D E : F ⟶ G) :
    homToHom a (D + E) = homToHom a D + homToHom a E :=
  rfl

end FiniteOrderDifferentialOperatorCat

end AlgebraicGeometry.Scheme.Hom
