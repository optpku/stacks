/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Invariant.Galois
public import ReasLib.Algebra.Group.Action.Stabilizer
public import ReasLib.RingTheory.LocalRing.ResidueField.LiesOver

@[expose] public section

/-!
# Residue fields of invariant ring extensions

@stack 0BRJ

This leaf specializes Mathlib's fraction-ring invariant theory to residue
fields at a lying-over pair.  It hides the quotient-algebra scalar towers but
keeps the induced residue-field algebra scoped, since that structure depends
on the chosen pair of primes.
-/

open scoped Pointwise

universe u v

namespace Ideal.ResidueField.Invariant

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]

/-- Residue fields at a lying-over pair form a normal extension for a finite
invariant action.  `Normal` includes algebraicity of the extension. -/
@[stacks 0BRJ "normal residue-field extension for an invariant action"]
theorem normal
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [Algebra.IsInvariant A B G]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    -- Local instance justification (defeq pin): select the canonical residue algebra of the lying-over pair for `Normal`.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    Normal p.ResidueField q.ResidueField := sorry
-- Proof strategy: install the quotient algebra and the two scalar towers from
-- `Ideal.ResidueField.LiesOver`; then specialize `Ideal.IsFractionRing.normal G p q` to the
-- fraction fields `p.ResidueField` and `q.ResidueField`.

/-- The canonical homomorphism from the stabilizer of `q` to the automorphism
group of `κ(q) / κ(p)`.

Only the action and scalar-commutation hypotheses are needed to define the
map; finiteness and invariance enter only in its surjectivity theorem. -/
@[stacks 0BRJ "stabilizer action on a residue-field extension"]
noncomputable def stabilizerHom
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    -- Local instance justification (defeq pin): select the canonical residue algebra used by the stabilizer action.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    MulAction.stabilizer G q →* Gal(q.ResidueField / p.ResidueField) :=
  -- Local instance justification (defeq pin): use the same `algebraOfLiesOver p q` as the declared residue-field action.
  letI : Algebra p.ResidueField q.ResidueField :=
    Ideal.ResidueField.algebraOfLiesOver p q
  -- Local instance justification (defeq pin): install the quotient algebra through which the residue action is induced.
  letI : Algebra (A ⧸ p) q.ResidueField :=
    Ideal.ResidueField.LiesOver.quotientAlgebra p q
  -- Local instance justification (defeq pin): use the residue-field scalar tower attached to `p` and `q`.
  letI : IsScalarTower (A ⧸ p) p.ResidueField q.ResidueField :=
    Ideal.ResidueField.LiesOver.isScalarTower_residue p q
  -- Local instance justification (defeq pin): use the quotient scalar tower attached to the same lying-over pair.
  letI : IsScalarTower (A ⧸ p) (B ⧸ q) q.ResidueField :=
    Ideal.ResidueField.LiesOver.isScalarTower_quotient p q
  IsFractionRing.stabilizerHom G p q p.ResidueField q.ResidueField

/-- On a class represented by `x : B`, `stabilizerHom` acts by applying the
corresponding element of the stabilizer to `x`. -/
@[simp, stacks 0BRJ "stabilizer action on residue-field representatives"]
theorem stabilizerHom_apply_mk
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (σ : MulAction.stabilizer G q) (x : B) :
    -- Local instance justification (defeq pin): select the residue algebra required to compare representatives.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    stabilizerHom G p q σ
        (algebraMap (B ⧸ q) q.ResidueField (Ideal.Quotient.mk q x)) =
      algebraMap (B ⧸ q) q.ResidueField
        (Ideal.Quotient.mk q (σ.1 • x)) := sorry
-- Proof strategy: unfold `stabilizerHom`, install the same quotient algebra and scalar towers, and
-- apply `IsFractionRing.stabilizerHom_apply_apply_mk`.

/-- For a finite invariant action, the stabilizer of `q` surjects onto
`Aut(κ(q) / κ(p))`. -/
@[stacks 0BRJ "surjective stabilizer action on a residue-field extension"]
theorem stabilizerHom_surjective
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    -- Local instance justification (defeq pin): select the canonical residue algebra for the finite invariant action.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    Function.Surjective (stabilizerHom G p q) := sorry
-- Proof strategy: unfold `stabilizerHom`, install the lying-over quotient algebra and scalar
-- towers, and apply `IsFractionRing.stabilizerHom_surjective G p q` to the two residue fields.

/-- When the whole group fixes `q`, its action on the induced residue-field extension is the
stabilizer action composed with the canonical map into `MulAction.stabilizer G q`. -/
@[reducible, stacks 0BRJ "residue-field action at a globally fixed prime"]
noncomputable def homOfFixed
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (hfixed : ∀ g : G, g • q = q) :
    -- Local instance justification (defeq pin): select the residue algebra used by the globally fixed-prime action.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    G →* Gal(q.ResidueField / p.ResidueField) :=
  -- Local instance justification (defeq pin): use the same residue algebra in the composite through the stabilizer.
  letI : Algebra p.ResidueField q.ResidueField :=
    Ideal.ResidueField.algebraOfLiesOver p q
  (stabilizerHom G p q).comp (MulAction.stabilizerHomOfFixed q hfixed)

/-- If the whole group fixes `q` and the inertia subgroup at `q` is trivial, its canonical action
identifies the group with the Galois group of the residue-field extension. -/
@[stacks 0BRJ "bijective residue-field action at a globally fixed prime"]
theorem homOfFixed_bijective
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (hfixed : ∀ g : G, g • q = q) (hinertia : q.inertia G = ⊥) :
    -- Local instance justification (defeq pin): select the residue algebra for the bijectivity statement.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    Function.Bijective (homOfFixed G p q hfixed) := sorry
-- Proof strategy: `MulAction.stabilizerHomOfFixed q hfixed` is bijective because it is the
-- identity on ambient group elements.  Its composite with `stabilizerHom` is surjective by
-- `stabilizerHom_surjective`.  For injectivity, rewrite the kernel of the stabilizer action with
-- `IsFractionRing.ker_stabilizerHom`; under the globally-fixed identification this is
-- `q.inertia G`, and `hinertia = ⊥` makes the kernel trivial.

/-- The stabilizer modulo inertia is canonically isomorphic to the Galois group of the induced
residue-field extension.  The local instances select the algebra and scalar towers attached to
this lying-over pair; no competing residue-field algebra instance is registered globally. -/
@[stacks 0BRJ "stabilizer quotient as a residue-field Galois group"]
noncomputable def stabilizerQuotientInertiaEquiv
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    -- Local instance justification (defeq pin): select the residue algebra for the quotient equivalence.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    MulAction.stabilizer G q ⧸ q.inertia (MulAction.stabilizer G q) ≃*
      Gal(q.ResidueField / p.ResidueField) :=
  -- Local instance justification (defeq pin): use the same residue algebra as the quotient equivalence's target action.
  letI : Algebra p.ResidueField q.ResidueField :=
    Ideal.ResidueField.algebraOfLiesOver p q
  -- Local instance justification (defeq pin): install the quotient algebra used by the quotient-action construction.
  letI : Algebra (A ⧸ p) q.ResidueField :=
    Ideal.ResidueField.LiesOver.quotientAlgebra p q
  -- Local instance justification (defeq pin): install the residue scalar tower required by the fraction-field equivalence.
  letI : IsScalarTower (A ⧸ p) p.ResidueField q.ResidueField :=
    Ideal.ResidueField.LiesOver.isScalarTower_residue p q
  -- Local instance justification (defeq pin): install the quotient scalar tower required by the same equivalence.
  letI : IsScalarTower (A ⧸ p) (B ⧸ q) q.ResidueField :=
    Ideal.ResidueField.LiesOver.isScalarTower_quotient p q
  IsFractionRing.stabilizerQuotientInertiaEquiv G p q
    p.ResidueField q.ResidueField

/-- On a stabilizer representative, `stabilizerQuotientInertiaEquiv` agrees with the canonical
residue-field action. -/
@[stacks 0BRJ "residue-field stabilizer quotient on representatives"]
theorem stabilizerQuotientInertiaEquiv_mk
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (sigma : MulAction.stabilizer G q) :
    -- Local instance justification (defeq pin): select the residue algebra for the representative quotient action.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    stabilizerQuotientInertiaEquiv G p q (QuotientGroup.mk sigma) =
      stabilizerHom G p q sigma := sorry
-- Proof strategy: unfold `stabilizerQuotientInertiaEquiv` and `stabilizerHom`, then apply
-- `IsFractionRing.stabilizerQuotientInertiaEquiv_mk`; both constructions use the same locally
-- pinned residue-field algebra and scalar towers.

end Ideal.ResidueField.Invariant
