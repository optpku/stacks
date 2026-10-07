module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.SetTheory.Cardinal.ToNat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.Basic
public import ReasLib.RingTheory.FittingIdeal.Basic

/-!
# Fitting-indexed affine smoothings of local complete intersections
-/

@[expose]
public section

universe u v

namespace Algebra.IsCompleteIntersectionOver

/-- Lemma 93.17.5: Let `k` be a field and let `A` be a local `k`-algebra essentially of finite
type which is a complete intersection over `k`. Set
`d = ringKrullDim A + Cardinal.toNat (Algebra.trdeg k (IsLocalRing.ResidueField A))`,
where `IsLocalRing.ResidueField A` is the residue field of `A`. Then there exist an integer `n`
and a flat, essentially of finite type `PowerSeries k`-algebra `B` whose special fibre
`B ⧸ Ideal.span {algebraMap PowerSeries.X}` is isomorphic to `A` as a `k`-algebra, such that
`algebraMap (PowerSeries.X ^ n)` lies in `fittingIdeal B (KaehlerDifferential (PowerSeries k) B) d`.
Here `PowerSeries k` is `k[[t]]` and `PowerSeries.X` is `t`. -/
@[stacks 0E7X]
theorem exists_flat_essFiniteType_fitting {k : Type u} [Field k] {A : Type v}
    [CommRing A] [Algebra k A] [IsLocalRing A] [Algebra.EssFiniteType k A]
    [IsCompleteIntersectionOver k A] (d : ℕ)
    (hd : ringKrullDim A +
        (Cardinal.toNat (Algebra.trdeg k (IsLocalRing.ResidueField A)) : WithBot ℕ∞) = d) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra (PowerSeries k) B)
      (_ : Algebra k B) (_ : IsScalarTower k (PowerSeries k) B)
      (_ : Module.Flat (PowerSeries k) B) (_ : Algebra.EssFiniteType (PowerSeries k) B)
      (e : (B ⧸ Ideal.span {(algebraMap (PowerSeries k) B) (PowerSeries.X : PowerSeries k)}) ≃ₐ[k] A)
      (n : ℕ),
      algebraMap (PowerSeries k) B (PowerSeries.X ^ n) ∈
        fittingIdeal B (KaehlerDifferential (PowerSeries k) B) d :=
  sorry

end Algebra.IsCompleteIntersectionOver
