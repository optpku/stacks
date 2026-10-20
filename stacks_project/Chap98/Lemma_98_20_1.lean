module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalityObstruction.Sequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open RingedSpace.Module
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/- Lemma 98.20.1: an infinite sequence of first-order thickenings with
residue-field kernels and no local retractions detects failure of versality. -/
@[stacks 0G2S] #check
  (AlgebraicGeometry.GroupoidsOver.exists_firstOrderThickeningSequence_of_not_isVersalAt :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] {U : Scheme.{u}} [IsAffine U]
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u : ℕ → U)
    (hu : ∀ n, IsFiniteTypePoint (u n))
    (hns : ∀ ⦃n m⦄, n ≠ m → ¬ Specializes (u n) (u m))
    (h : ∀ n, ¬ IsVersalAt hU x hx (u n)),
    ∃ (Useq : ℕ → Scheme.{u}) (hUseq : ∀ n, Useq n ⟶ S)
      (iU : ∀ n, U ⟶ Useq n) (hiU : ∀ n, iU n ≫ hUseq n = hU)
      (step : ∀ n, Useq n ⟶ Useq (n + 1))
      (hstep : ∀ n, step n ≫ hUseq (n + 1) = hUseq n)
      (h_comp : ∀ n, iU (n + 1) = iU n ≫ step n)
      (xseq : ℕ → X.total)
      (hxseq : ∀ n, X.p.obj (xseq n) = Over.mk (hUseq n))
      (Φ : ∀ n, x ⟶ xseq n) (φ : ∀ n, xseq n ⟶ xseq (n + 1)),
      (∀ n, X.p.IsHomLift (Over.homMk (iU n) (hiU n) : Over.mk hU ⟶ Over.mk (hUseq n)) (Φ n)) ∧
        (∀ n, X.p.IsHomLift (Over.homMk (step n) (hstep n) : Over.mk (hUseq n) ⟶ Over.mk (hUseq (n + 1))) (φ n)) ∧
          (∀ n, Φ (n + 1) = Φ n ≫ φ n) ∧
            (∀ n, IsFirstOrderThickening (iU n)) ∧
              Nonempty ((iU 0).ker.toModule ≅
                Scheme.Modules.residueFieldSkyscraper ((iU 0).base (u 0))) ∧
                (∀ n, IsFirstOrderThickening (step n)) ∧
                  (∀ n, Nonempty ((step n).ker.toModule ≅
                    Scheme.Modules.residueFieldSkyscraper
                      ((step n).base ((iU n).base (u (n + 1)))))) ∧
                    ∀ n, ¬ existsLocalRetraction (hiU n) hx (hxseq n) (Φ n) (u n))

end AlgebraicGeometry.GroupoidsOver
