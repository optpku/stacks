/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Cohomology.Galois

/-!
# Lemma 61.22.1

Pro-étale cohomology of completed Galois sheaves agrees with continuous Galois
cohomology for profinite and adically complete coefficients.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

section Profinite

variable (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M]
  [TotallyDisconnectedSpace M] [DistribMulAction (Gal(Ksep / K)) M]
  [ContinuousSMul (Gal(Ksep / K)) M]

/- Lemma 61.22.1 (1) -/
@[stacks 09B4]
#check (AlgebraicGeometry.Scheme.ProEt.profiniteGaloisSheaf_proetaleCohomology K Ksep M :
  ∀ i : ℕ,
    IsIsomorphic
      (proEtaleCohomology (Spec (.of K)) (profiniteGaloisSheaf K Ksep M) i)
      (ContinuousCohomology.abelian (Gal(Ksep / K))
        (ContinuousModule.profiniteTopRep (Gal(Ksep / K)) M) i))

end Profinite

section Adic

variable (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep] (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  (I : Ideal Λ) (M : Type u) [AddCommGroup M] [Module Λ M]
  [IsAdicComplete I M] [DistribMulAction (Gal(Ksep / K)) M]
  [SMulCommClass (Gal(Ksep / K)) Λ M]
  [hcont : @ContinuousSMul (Gal(Ksep / K)) M _ _ (Ideal.adicModuleTopology I M)]

/- Lemma 61.22.1 (2) -/
@[stacks 09B4]
#check (AlgebraicGeometry.Scheme.ProEt.completedGaloisSheaf_proetaleCohomology K Ksep Λ I M :
  ∀ i : ℕ,
    IsIsomorphic
      (ModuleCat.of Λ
        (proEtaleCohomology (Spec (.of K)) (completedGaloisSheaf K Ksep I M) i))
      (ModuleCat.of Λ
        (ContinuousCohomology.abelian (Gal(Ksep / K))
          (ContinuousModule.adicTopRep (Gal(Ksep / K)) I M) i)))

end Adic

end AlgebraicGeometry.Scheme.ProEt

end
