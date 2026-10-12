/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.SetTheory.Cardinal.ENat
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.QuasiCompact
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.RingTheory.Henselian.StrictHenselian

/-!
# Gabber's cohomological bound on the locally finite type étale site

Finite invertible coefficients, the allowed arithmetic bases, and the explicit bound governing
cohomology on quasi-compact objects.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The order of a finite coefficient ring `Λ` is invertible in the global sections of `S`. -/
def orderInvertible (S : Scheme.{u}) (Λ : Type u) [Ring Λ] [Finite Λ] : Prop :=
  IsUnit (Nat.card Λ : Γ(S, ⊤))

/-- Invertibility of the coefficient-ring order is the defining global-sections condition. -/
theorem orderInvertible_iff (S : Scheme.{u}) (Λ : Type u) [Ring Λ] [Finite Λ] :
    orderInvertible S Λ ↔ IsUnit (Nat.card Λ : Γ(S, ⊤)) :=
  sorry

/-- Allowed bases for the finite-coefficient étale cohomological bound. -/
inductive IsFiniteEtaleCoefficientBase (S : Scheme.{u}) : Prop where
  /-- A spectrum of a finite field. -/
  | ofFiniteField (K : Type u) [Field K] [Finite K]
      (e : S ≅ Scheme.Spec.obj (op (CommRingCat.of K)))
  /-- A spectrum of a separably closed field. -/
  | ofSeparablyClosed (K : Type u) [Field K] [IsSepClosed K]
      (e : S ≅ Scheme.Spec.obj (op (CommRingCat.of K)))
  /-- A spectrum of a strictly henselian Noetherian local ring. -/
  | ofStrictlyHenselian (R : Type u) [CommRing R] [IsNoetherianRing R]
      [StrictHenselianLocalRing R] (e : S ≅ Scheme.Spec.obj (op (CommRingCat.of R)))
  /-- A spectrum of a henselian Noetherian local ring with finite residue field. -/
  | ofHenselianFiniteResidue (R : Type u) [CommRing R] [IsNoetherianRing R]
      [HenselianLocalRing R] [Finite (IsLocalRing.ResidueField R)]
      (e : S ≅ Scheme.Spec.obj (op (CommRingCat.of R)))

/-- Every finite-coefficient étale base in the four spectral families is affine. -/
theorem IsFiniteEtaleCoefficientBase.isAffine {S : Scheme.{u}}
    (hS : IsFiniteEtaleCoefficientBase S) : IsAffine S :=
  sorry

/-- The transcendence degree of the residue-field extension at a point of `V`. -/
def residueExtensionTrdeg {S : Scheme.{u}} (V : locallyOfFiniteTypeOver S) (v : V.left) :
    WithBot ℕ∞ :=
  (@Algebra.trdeg (S.residueField (V.hom v) : Type u) (V.left.residueField v : Type u) _ _
      (RingHom.toAlgebra (V.hom.residueFieldMap v).hom)).toENat

/-- The explicit extended-valued Gabber dimension formula for a locally finite type object. -/
def cohomologyBoundFormula {S : Scheme.{u}} (V : locallyOfFiniteTypeOver S) : WithBot ℕ∞ :=
  1 + 2 * topologicalKrullDim S +
    (⨆ v, residueExtensionTrdeg V v + 2 * ringKrullDim (V.left.presheaf.stalk v))

/-- The natural-valued bound obtained by truncating the extended-valued Gabber formula. -/
def cohomologyBound {S : Scheme.{u}} (V : locallyOfFiniteTypeOver S) : ℕ :=
  ((cohomologyBoundFormula V).unbotD 0).toNat

/-- When the formula has finite natural value `n`, the truncated bound is `n`. -/
theorem cohomologyBound_spec {S : Scheme.{u}} (V : locallyOfFiniteTypeOver S) {n : ℕ}
    (hn : cohomologyBoundFormula V = n) :
    cohomologyBound V = n :=
  sorry

/-- Under the allowed-base hypotheses, the formula agrees with the natural bound on a nonempty
quasi-compact object. -/
theorem cohomologyBoundFormula_eq_cohomologyBound {S : Scheme.{u}}
    (hS : IsFiniteEtaleCoefficientBase S) {V : locallyOfFiniteTypeOver S}
    (hV : quasiCompact S V) (hVne : Nonempty V.left) :
    cohomologyBoundFormula V = cohomologyBound V :=
  sorry

/-- Above the Gabber bound, objectwise cohomology vanishes for every module sheaf on the slice. -/
theorem higherCohomology_isZero {S : Scheme.{u}} {Λ : Type u} [Ring Λ] [Finite Λ]
    [HasWeakSheafify (etaleTopology S) RingCat.{u}]
    (hS : IsFiniteEtaleCoefficientBase S) (hΛ : orderInvertible S Λ)
    {V : locallyOfFiniteTypeOver S} (hV : quasiCompact S V)
    [HasSheafify ((etaleTopology S).over V) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf ((etaleTopology S).over V) AddCommGrpCat.{u})]
    {cover : FormalCoproduct.{u} (Over V)} (hcover : cover ∈ coveringSystem S V)
    (i : cover.I) (p : ℕ) (hp : cohomologyBound V < p)
    (ℱ : SheafOfModules.{u} ((constantRingSheaf S Λ).over V)) :
    IsZero
      (Sheaf.cohomologyOverObject
        ((SheafOfModules.toSheaf ((constantRingSheaf S Λ).over V)).obj ℱ)
        (cover.obj i) p) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
