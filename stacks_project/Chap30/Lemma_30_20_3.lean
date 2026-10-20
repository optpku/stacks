module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealPower.AffineComparison
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open AlgebraicGeometry.Scheme

universe u

/- Lemma 30.20.3: let `A` be a Noetherian ring, `I ⊂ A` an ideal, `f : X ⟶ Spec A`
proper, and `F` coherent on `X`. Then for every `p` there is some `c` such that
Rees multiplication `I^(n-c) ⊗ H^p(X, I^c F) ⟶ H^p(X, I^n F)` is surjective for
`n ≥ c`, images of `H^p(I^(n+m) F) ⟶ H^p(I^n F)` lie in `I^(m-e) H^p(I^n F)`
with `e = max(0, c-n)` whenever `n+m ≥ c`, kernels of the maps to `H^p(F)` and
to `H^p(I^(n-c) F)` agree for `n ≥ c`, there are maps `I^n H^p(F) ⟶ H^p(I^(n-c) F)`
whose two stable-range composites for `n ≥ 2c` are the canonical transitions,
and the inverse systems `(H^p(I^n F))` and `(I^n H^p(F))` are pro-isomorphic. -/
@[stacks 02OA] #check (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.existsComparison :
  ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [IsNoetherianRing A] (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ),
    ∃ c : ℕ, Nonempty (Hom.IdealPowerCohomology.Comparison I f F p c))

#check @Hom.IdealPowerCohomology.mulMap
#check @Hom.IdealPowerCohomology.Comparison.image_le
#check @Hom.IdealPowerCohomology.Comparison.ker_eq
#check @Hom.IdealPowerCohomology.Comparison.reverseAt
#check @Hom.IdealPowerCohomology.Comparison.reverse_forward
#check @Hom.IdealPowerCohomology.Comparison.forward_reverse
#check @Hom.IdealPowerCohomology.Comparison.toProIso
