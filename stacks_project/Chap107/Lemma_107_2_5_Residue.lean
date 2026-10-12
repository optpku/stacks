/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import stacks_project.Chap98.«98_3_0_1_Factorization»
public import stacks_project.Chap98.Definition_98_9_1_AlgebraHom
public import stacks_project.Chap100.Lemma_100_4_1_FieldValuedPoint

/-!
# Residue-field restriction of field-valued points

A field extension `k → l` induces the restricted field-valued point
`x_{l,0}` of an algebraic stack, together with the predicate that a
morphism of complete local `S`-algebras induces a given residue-field
extension over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.FieldValuedPoint

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- The morphism `Spec(l) ⟶ Spec(k)` induced by a field extension `k → l`. -/
def restrictSchemeHom (x0 : FieldValuedPoint X) (l : Type u) [Field l]
    [Algebra x0.K l] : Spec (.of l) ⟶ Spec (.of x0.K) :=
  Spec.map (CommRingCat.ofHom (algebraMap x0.K l))

/-- `restrictSchemeHom` is `Spec` of the structure map `k → l`. -/
theorem restrictSchemeHom_eq (x0 : FieldValuedPoint X) (l : Type u) [Field l]
    [Algebra x0.K l] :
    restrictSchemeHom x0 l = Spec.map (CommRingCat.ofHom (algebraMap x0.K l)) :=
  sorry

/-- The morphism `Over.mk (Spec(l) ⟶ S) ⟶ Over.mk (Spec(k) ⟶ S)` with left
component `restrictSchemeHom`. -/
def restrictOverHom (x0 : FieldValuedPoint X) (l : Type u) [Field l]
    [Algebra x0.K l] :
    Over.mk (restrictSchemeHom x0 l ≫ x0.structureHom) ⟶ Over.mk x0.structureHom :=
  Over.homMk (restrictSchemeHom x0 l) rfl

/-- `restrictOverHom` has left component `restrictSchemeHom`. -/
theorem restrictOverHom_left (x0 : FieldValuedPoint X) (l : Type u) [Field l]
    [Algebra x0.K l] :
    (restrictOverHom x0 l).left = restrictSchemeHom x0 l := sorry

/-- The field-valued point `x_{l,0}` induced by a field extension `l / k` of
the source of `x0`. -/
def restrict (x0 : FieldValuedPoint X) (l : Type u) [Field l] [Algebra x0.K l] :
    FieldValuedPoint X where
  K := l
  structureHom := restrictSchemeHom x0 l ≫ x0.structureHom
  hom := overMap (restrictOverHom x0 l) ≫ x0.hom

/-- The induced point `x0.restrict l` has source field `l`, structure morphism
`Spec(l) ⟶ Spec(k) ⟶ S`, and 1-morphism obtained by precomposing `x0.hom`
with `overMap`. -/
theorem restrict_spec (x0 : FieldValuedPoint X) (l : Type u) [Field l]
    [Algebra x0.K l] :
    (x0.restrict l).K = l ∧
      (x0.restrict l).structureHom = restrictSchemeHom x0 l ≫ x0.structureHom ∧
        (x0.restrict l).hom = overMap (restrictOverHom x0 l) ≫ x0.hom :=
  sorry

/-- The induced morphism `x_{l,0} → x0` as a factorization of field-valued
points over `S`. -/
def restrictFactorization (x0 : FieldValuedPoint X) (l : Type u) [Field l]
    [Algebra x0.K l] : Factorization (x0.restrict l) x0 :=
  Factorization.of (restrictSchemeHom x0 l) rfl (Iso.refl _)

/-- `restrictFactorization` is `Spec` of `k → l` and the triangle over `S`
commutes. -/
theorem restrictFactorization_spec (x0 : FieldValuedPoint X) (l : Type u)
    [Field l] [Algebra x0.K l] :
    (x0.restrictFactorization l).schemeHom = restrictSchemeHom x0 l ∧
      (x0.restrictFactorization l).schemeHom ≫ x0.structureHom =
        (x0.restrict l).structureHom :=
  sorry

/-- Finite extensions of a finite-type field over `S` remain locally of finite
type over `S`. -/
instance instLocallyOfFiniteType_restrict (x0 : FieldValuedPoint X)
    (l : Type u) [Field l] [Algebra x0.K l]
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    [Module.Finite x0.K l] :
    AlgebraicGeometry.LocallyOfFiniteType (x0.restrict l).structureHom :=
  sorry

end AlgebraicGeometry.AlgebraicStack.FieldValuedPoint

namespace AlgebraicGeometry.CompleteLocalSAlgebra.Hom

variable {S : Scheme.{u}}

/-- An `S`-algebra map `A → A'` induces a given field extension `l / k` when
the residue fields of `A` and `A'` may be identified with `k` and `l` over
`S` so that `ResidueField.map` recovers `algebraMap k l`. -/
def InducesResidueExtension {A A' : CompleteLocalSAlgebra S} (φ : Hom A' A)
    (k l : Type u) [Field k] [Field l] [Algebra k l]
    (σk : Spec (.of k) ⟶ S) (σl : Spec (.of l) ⟶ S) : Prop :=
  ∃ (e : ResidueField A.carrier ≃+* k) (e' : ResidueField A'.carrier ≃+* l),
    residueSpecMap e ≫ A.toS = σk ∧
      residueSpecMap e' ≫ A'.toS = σl ∧
        e'.toRingHom.comp (ResidueField.map φ.hom) =
          (algebraMap k l).comp e.toRingHom

/-- Inducing a residue-field extension unpacks to residue identifications over
`S` whose `ResidueField.map` square is `algebraMap k l`. -/
theorem inducesResidueExtension_iff {A A' : CompleteLocalSAlgebra S}
    (φ : Hom A' A) (k l : Type u) [Field k] [Field l] [Algebra k l]
    (σk : Spec (.of k) ⟶ S) (σl : Spec (.of l) ⟶ S) :
    InducesResidueExtension φ k l σk σl ↔
      ∃ (e : ResidueField A.carrier ≃+* k)
        (e' : ResidueField A'.carrier ≃+* l),
        residueSpecMap e ≫ A.toS = σk ∧
          residueSpecMap e' ≫ A'.toS = σl ∧
            e'.toRingHom.comp (ResidueField.map φ.hom) =
              (algebraMap k l).comp e.toRingHom :=
  sorry

end AlgebraicGeometry.CompleteLocalSAlgebra.Hom
