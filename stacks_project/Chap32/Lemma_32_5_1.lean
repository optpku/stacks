module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Approximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 32.5.1 (1): for an open immersion `f : W ⟶ Spec(R)` with `W` finite type over
`Spec(ℤ)`, some finite type `ℤ`-subalgebra of `R` induces an open immersion from `W`. -/
@[stacks 01Z7] #check
  (AlgebraicGeometry.Scheme.Hom.finiteTypeZSubalgebraStages_nonempty :
    ∀ {W : AlgebraicGeometry.Scheme.{u}} {R : Type u} [CommRing R]
      (f : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)),
      [AlgebraicGeometry.IsOpenImmersion f] →
        [AlgebraicGeometry.Scheme.Hom.FiniteType
          (AlgebraicGeometry.specULiftZIsTerminal.from W)] →
          (AlgebraicGeometry.Scheme.Hom.finiteTypeZSubalgebraStages f).Nonempty)

/- Lemma 32.5.1 (2): these finite type `ℤ`-subalgebras are directed by inclusion and have
supremum equal to the whole ambient ring. -/
@[stacks 01Z7] #check
  (AlgebraicGeometry.Scheme.Hom.finiteTypeZSubalgebraStages_directed_and_sSup_eq_top :
    ∀ {W : AlgebraicGeometry.Scheme.{u}} {R : Type u} [CommRing R]
      (f : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)),
      [AlgebraicGeometry.IsOpenImmersion f] →
        [AlgebraicGeometry.Scheme.Hom.FiniteType
          (AlgebraicGeometry.specULiftZIsTerminal.from W)] →
          DirectedOn (· ≤ ·)
              (AlgebraicGeometry.Scheme.Hom.finiteTypeZSubalgebraStages f) ∧
            sSup (AlgebraicGeometry.Scheme.Hom.finiteTypeZSubalgebraStages f) = ⊤)
