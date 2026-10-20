module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Group

/-!
# Torsion in the Picard group of a smooth projective curve

This module records the torsion classification of the Picard group of a smooth
projective curve over an algebraically closed field.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Curve

/-- For a smooth projective curve over an algebraically closed field, prime-to-characteristic
torsion in the Picard group is a free `ZMod n`-module of rank `2 * genus X`. -/
theorem picardTorsionEquiv {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]
    (n : ℕ) (h_n : 1 ≤ n) (h_unit : IsUnit (n : k)) :
    Nonempty
      (AddSubgroup.torsionBy X.left.PicardGroup (n : ℤ) ≃+
        (Fin (2 * genus X) → ZMod n)) := sorry

/-- In prime characteristic, the `p ^ m`-torsion in the Picard group of a smooth projective
curve has a fixed rank at most `genus X`, independent of the positive exponent `m`. -/
theorem existsPicardPRank {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ f : ℕ, f ≤ genus X ∧ ∀ m : ℕ, 1 ≤ m →
      Nonempty
        (AddSubgroup.torsionBy X.left.PicardGroup ((p ^ m : ℕ) : ℤ) ≃+
          (Fin f → ZMod (p ^ m))) := sorry

end AlgebraicGeometry.Curve
