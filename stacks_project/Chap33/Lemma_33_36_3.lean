module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Properties
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Lemma 33.36.3 compatibility entry point

The reusable absolute-Frobenius property instances are owned by
`ReasLib.AlgebraicGeometry.Scheme.Frobenius.Properties`.
-/

/- Lemma 33.36.3: In prime characteristic, the absolute Frobenius is a universal
homeomorphism, is integral, and induces purely inseparable residue field extensions. -/
@[stacks 0CC8]
#check (AlgebraicGeometry.absoluteFrobenius_universalHomeomorphism :
  ∀ {p : ℕ} [Fact p.Prime] {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.Scheme.IsCharP X p],
    AlgebraicGeometry.UniversalHomeomorphism
      (AlgebraicGeometry.Scheme.absoluteFrobenius p X))

#check (AlgebraicGeometry.absoluteFrobenius_isIntegralHom :
  ∀ {p : ℕ} [Fact p.Prime] {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.Scheme.IsCharP X p],
    AlgebraicGeometry.IsIntegralHom
      (AlgebraicGeometry.Scheme.absoluteFrobenius p X))

#check (AlgebraicGeometry.absoluteFrobenius_residueField_isPurelyInseparable :
  ∀ {p : ℕ} [Fact p.Prime] {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.Scheme.IsCharP X p] (x : X),
    IsPurelyInseparable
      (X.residueField ((AlgebraicGeometry.Scheme.absoluteFrobenius p X) x))
      (X.residueField x))
