/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Infinitesimal
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

/- Lemma 38.28.8: let `A_lim` realize a sequential inverse system `A` as its limit,
where the transition maps are surjective with locally nilpotent kernels. A locally finite
type monomorphism `f : T ⟶ Spec A_lim.cone.pt` is an isomorphism if every finite-stage
spectrum factors through `f`. -/
@[stacks 0CTJ] #check
  (AlgebraicGeometry.Scheme.Limit.isIso_of_stageSpectrum_factorizations :
    ∀ (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
      (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
      (T : Scheme.{u}) (f : T ⟶ Spec A_lim.cone.pt) [Mono f] [LocallyOfFiniteType f]
      (h_factor : ∀ n, ∃ g : Spec (A.obj (Opposite.op n)) ⟶ T,
        g ≫ f = Spec.map (A_lim.cone.stageMap n)),
      IsIso f)
