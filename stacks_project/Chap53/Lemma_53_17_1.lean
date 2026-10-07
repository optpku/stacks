module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Torsion

@[expose] public section

universe u

namespace AlgebraicGeometry.Curve

/- Lemma 53.17.1 (1): if `n ≥ 1` is invertible in an algebraically closed field `k`,
the `n`-torsion in the Picard group of a smooth projective curve `X` is additively
equivalent to `2 * genus X` copies of `ZMod n`. -/
@[stacks 0C1Z] #check
  (AlgebraicGeometry.Curve.picardTorsionEquiv :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Smooth X.hom] [Projective X.hom] (n : ℕ)
      (h_n : 1 ≤ n) (h_unit : IsUnit (n : k)),
      Nonempty
        (AddSubgroup.torsionBy X.left.PicardGroup (n : ℤ) ≃+
          (Fin (2 * genus X) → ZMod n)))

/- Lemma 53.17.1 (2): in characteristic `p`, the `p ^ m`-torsion in the Picard group
of a smooth projective curve `X` has one fixed rank `f ≤ genus X` for every `m ≥ 1`. -/
@[stacks 0C1Z] #check
  (AlgebraicGeometry.Curve.existsPicardPRank :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Smooth X.hom] [Projective X.hom] (p : ℕ)
      [Fact p.Prime] [CharP k p],
      ∃ f : ℕ, f ≤ genus X ∧ ∀ m : ℕ, 1 ≤ m →
        Nonempty
          (AddSubgroup.torsionBy X.left.PicardGroup ((p ^ m : ℕ) : ℤ) ≃+
            (Fin f → ZMod (p ^ m))))

end AlgebraicGeometry.Curve
