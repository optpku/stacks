/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Fibre degrees of morphisms from schemes to algebraic spaces

This file owns the chosen field-valued fibre `Spec(k) ×_X U` of a morphism
`ofOver U ⟶ X`, its structure map to `Spec(k)`, and the uniform fibre-degree
boundedness predicates.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Binary products of schemes over `S` are the fibre products over `S`. -/
instance hasBinaryProducts_over (S : Scheme.{u}) : HasBinaryProducts (Over S) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

end AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- A morphism from a scheme to an algebraic space is relatively representable, by the
representable-diagonal criterion. -/
def hom_relativelyRepresentable (f : ofOver U ⟶ X) :
    yoneda.relativelyRepresentable f :=
  Functor.relativelyRepresentable.of_diag X.representableDiagonal f

/-- Relative representability of a morphism from a scheme is the diagonal criterion on `X`. -/
theorem hom_relativelyRepresentable_eq (f : ofOver U ⟶ X) :
    hom_relativelyRepresentable f =
      Functor.relativelyRepresentable.of_diag X.representableDiagonal f :=
  sorry

/-- The chosen scheme `Spec(k) ×_X U` over `S`, as the represented pullback of `f` along a
field-valued point of `X`. -/
def fieldValuedPointPullback (f : ofOver U ⟶ X) (p : FieldValuedPoint X) : Over S :=
  (hom_relativelyRepresentable f).pullback p.hom

/-- The structure morphism of the chosen fibre over the source field `k`. -/
def fieldValuedPointPullbackSnd (f : ofOver U ⟶ X) (p : FieldValuedPoint X) :
    (fieldValuedPointPullback f p).left ⟶ Spec (.of p.K) :=
  ((hom_relativelyRepresentable f).snd p.hom).left

/-- The global-sections ring of the chosen field-valued fibre. -/
abbrev fieldValuedPointPullbackGlobalSections (f : ofOver U ⟶ X) (p : FieldValuedPoint X) :=
  Scheme.Γ.obj (op (fieldValuedPointPullback f p).left)

/-- The canonical `k`-algebra structure on global sections of the chosen fibre. -/
@[reducible]
instance fieldValuedPointPullbackGlobalSectionsAlgebra (f : ofOver U ⟶ X)
    (p : FieldValuedPoint X) :
    Algebra p.K (fieldValuedPointPullbackGlobalSections f p) :=
  Scheme.Hom.globalSectionsAlgebra (fieldValuedPointPullbackSnd f p)

/-- The degree of the chosen fibre over its source field, as a finite rank of global sections. -/
abbrev fieldValuedPointPullbackDegree (f : ofOver U ⟶ X) (p : FieldValuedPoint X) : ℕ :=
  Module.finrank p.K (fieldValuedPointPullbackGlobalSections f p)

/-- The represented pullback square identifying `fieldValuedPointPullback f p` with
`Spec(p.K) ×_X U`. -/
theorem fieldValuedPointPullback_isPullback (f : ofOver U ⟶ X) (p : FieldValuedPoint X) :
    IsPullback ((hom_relativelyRepresentable f).fst p.hom)
      (yoneda.map ((hom_relativelyRepresentable f).snd p.hom)) f p.hom :=
  sorry

/-- The fibre structure morphism is the underlying scheme map of the represented pullback
projection. -/
theorem fieldValuedPointPullbackSnd_eq (f : ofOver U ⟶ X) (p : FieldValuedPoint X) :
    fieldValuedPointPullbackSnd f p =
      ((hom_relativelyRepresentable f).snd p.hom).left :=
  sorry

/-- The fibre degree is the finite rank of the global-sections algebra over the source field. -/
theorem fieldValuedPointPullbackDegree_eq (f : ofOver U ⟶ X) (p : FieldValuedPoint X) :
    fieldValuedPointPullbackDegree f p =
      Module.finrank p.K (fieldValuedPointPullbackGlobalSections f p) :=
  sorry

/-- A number bounds the fibres of `f` when every field-valued fibre is finite of degree at most
that number. -/
def degreesOfFibresBoundedBy (f : ofOver U ⟶ X) (n : ℕ) : Prop :=
  ∀ p : FieldValuedPoint X,
    IsFinite (fieldValuedPointPullbackSnd f p) ∧ fieldValuedPointPullbackDegree f p ≤ n

/-- Unfold the pointwise finiteness and degree-bound condition. -/
theorem degreesOfFibresBoundedBy_iff (f : ofOver U ⟶ X) (n : ℕ) :
    degreesOfFibresBoundedBy f n ↔
      ∀ p : FieldValuedPoint X,
        IsFinite (fieldValuedPointPullbackSnd f p) ∧ fieldValuedPointPullbackDegree f p ≤ n :=
  sorry

/-- Extract finiteness of the fibre over a specified field-valued point from a degree bound. -/
theorem degreesOfFibresBoundedBy.isFinite {f : ofOver U ⟶ X} {n : ℕ}
    (h : degreesOfFibresBoundedBy f n) (p : FieldValuedPoint X) :
    IsFinite (fieldValuedPointPullbackSnd f p) :=
  sorry

/-- Extract the numerical degree bound at a specified field-valued point. -/
theorem degreesOfFibresBoundedBy.fiberDegree_le {f : ofOver U ⟶ X} {n : ℕ}
    (h : degreesOfFibresBoundedBy f n) (p : FieldValuedPoint X) :
    fieldValuedPointPullbackDegree f p ≤ n :=
  sorry

/-- A numerical fibre bound is equivalent to the same condition on raw fields and morphisms
`Spec(k) ⟶ X` over `S`. -/
theorem degreesOfFibresBoundedBy_iff_forall_fields (f : ofOver U ⟶ X) (n : ℕ) :
    degreesOfFibresBoundedBy f n ↔
      ∀ (k : Type u) [Field k] (σ : Spec (.of k) ⟶ S) (ξ : ofOver (Over.mk σ) ⟶ X),
        IsFinite (fieldValuedPointPullbackSnd f (FieldValuedPoint.of k σ ξ)) ∧
          fieldValuedPointPullbackDegree f (FieldValuedPoint.of k σ ξ) ≤ n :=
  sorry

/-- The fibres of a morphism from a scheme to an algebraic space are universally bounded when
one natural number bounds the degree of every field-valued fibre. -/
def universallyBoundedFibres (f : ofOver U ⟶ X) : Prop :=
  ∃ n : ℕ, degreesOfFibresBoundedBy f n

/-- Unfold universal fibre boundedness into the existence of a uniform field-valued degree
bound. -/
theorem universallyBoundedFibres_iff (f : ofOver U ⟶ X) :
    universallyBoundedFibres f ↔
      ∃ n : ℕ, ∀ p : FieldValuedPoint X,
        IsFinite (fieldValuedPointPullbackSnd f p) ∧ fieldValuedPointPullbackDegree f p ≤ n :=
  sorry

/-- When the target is a scheme, universal fibre boundedness recovers the scheme-morphism
predicate. -/
theorem universallyBoundedFibres_ofOverMap {V : Over S} (φ : U ⟶ V) :
    universallyBoundedFibres (ofOverMap φ) ↔ Scheme.Hom.universallyBoundedFibres φ.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
