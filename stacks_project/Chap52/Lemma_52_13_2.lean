module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealComplement.PrincipalCompletion
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 52.13.2: let `U = Spec A ∖ V(𝔞)`. If `f ∈ 𝔞`, `M` is finite,
`A` is `(f)`-adically complete, and a power of `f` annihilates every
`H^j_𝔞(M)` for `j ≤ s + 1`, then for every `i < s` the canonical map from
`H^i(U, M̃)` to the inverse limit of `H^i(U, (M ⧸ f ^ (n + 1) M)̃)` is bijective. -/
@[stacks 0EKM] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomologyComparison_bijective_of_localCohomology :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    [IsAdicComplete (Ideal.span {f}) A]
    (s i : ℕ)
    (h_ann : ∀ j : ℕ, j ≤ s + 1 →
      Module.IsAnnihilatedByPower (Ideal.span {f}) ((localCohomology 𝔞 j).obj M))
    (hi : i < s),
    Function.Bijective
      (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomologyComparison 𝔞 f M i))
