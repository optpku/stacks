module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import stacks_project.Chap61.Lemma_61_22_1_Comparison
public import stacks_project.Chap61.Lemma_61_22_1_Sheaf

/-!
# Lemma 61.22.1

Pro-étale cohomology of the completed Galois sheaf of a profinite abelian
continuous Galois module, or of an I-adically complete module, is Tate
continuous Galois cohomology.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt

noncomputable section

universe u

/-- Lemma 61.22.1 (1): if `M` is a profinite abelian group with a continuous
action of `G = Gal(k^sep/k)`, then the pro-étale cohomology of the completed
Galois sheaf `underline{M}^∧` on `Spec k_proétale` is Tate continuous Galois
cohomology `H^i_cont(G, M)`, as abelian groups. -/
@[stacks 09B4]
theorem profiniteGaloisSheaf_proetaleCohomology
    (k : Type u) [Field k] (s : GeometricPoint (Spec (.of k)))
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [CompactSpace M] [T2Space M] [TotallyDisconnectedSpace M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [ContinuousSMul s.absoluteGaloisGroup M] (i : ℕ) :
    IsIsomorphic
      (proEtaleCohomology (Spec (.of k)) (profiniteGaloisSheaf k s M) i)
      (continuousCohomologyAb s.absoluteGaloisGroup
        (profiniteGaloisTopRep k s M) i) := sorry

/-- Lemma 61.22.1 (2): if `Λ` is a Noetherian ring, `I ⊆ Λ` an ideal, and `M`
an `I`-adically complete `Λ`-module with a continuous action of
`G = Gal(k^sep/k)` for the `I`-adic topology, then the pro-étale cohomology of
the completed Galois sheaf `underline{M}^∧` on `Spec k_proétale` is Tate
continuous Galois cohomology `H^i_cont(G, M)`, as `Λ`-modules. -/
@[stacks 09B4]
theorem completedGaloisSheaf_proetaleCohomology
    (k : Type u) [Field k] (s : GeometricPoint (Spec (.of k)))
    (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ)
    (M : Type u) [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    [DistribMulAction s.absoluteGaloisGroup M]
    [SMulCommClass s.absoluteGaloisGroup Λ M]
    [hcont : @ContinuousSMul s.absoluteGaloisGroup M _ _ (Ideal.adicModuleTopology I M)]
    (i : ℕ) :
    IsIsomorphic
      (ModuleCat.of Λ
        (proEtaleCohomology (Spec (.of k)) (completedGaloisSheaf k s I M) i))
      (ModuleCat.of Λ
        (continuousCohomologyAb s.absoluteGaloisGroup
          (completedGaloisTopRep k s I M) i)) := sorry
