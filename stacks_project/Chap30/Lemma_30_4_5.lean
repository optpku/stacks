module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Vanishing
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 30.4.5 (1): higher direct images of quasi-coherent modules along quasi-compact and
quasi-separated morphisms are quasi-coherent. -/
@[stacks 01XJ] #check
  (AlgebraicGeometry.Scheme.higherDirectImageModule_isQuasicoherent_of_quasiCompact_quasiSeparated :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ),
      (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ p).IsQuasicoherent)

/- Lemma 30.4.5 (2): over a quasi-compact base, higher direct images of quasi-coherent modules
along a quasi-compact and quasi-separated morphism vanish above one degree. -/
@[stacks 01XJ] #check
  (AlgebraicGeometry.Scheme.eventually_higherDirectImageModule_isZero_of_quasiCompact_base :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      [CompactSpace S.carrier],
      ∃ n : ℕ, ∀ (ℱ : X.Modules), ℱ.IsQuasicoherent → ∀ p : ℕ, n ≤ p →
        CategoryTheory.Limits.IsZero
          (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ p))

/- Lemma 30.4.5 (3): the vanishing degree over a quasi-compact base can be chosen uniformly
after every base change. -/
@[stacks 01XJ] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.eventually_isZero_after_baseChange :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      [CompactSpace S.carrier],
      ∃ n : ℕ, ∀ ⦃S' : AlgebraicGeometry.Scheme.{u}⦄ (g : S' ⟶ S)
        (ℱ' : (CategoryTheory.Limits.pullback f g : AlgebraicGeometry.Scheme.{u}).Modules),
        ℱ'.IsQuasicoherent → ∀ p : ℕ, n ≤ p → CategoryTheory.Limits.IsZero
          (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule
            (CategoryTheory.Limits.pullback.snd f g).toShHom ℱ' p))
