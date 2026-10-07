module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GabberCriterion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

/- Lemma 59.80.2: if every local ring of `R` is strictly henselian and an abelian
sheaf `F` on `Spec R`_étale has vanishing kernel of the `H¹` restriction map
from `D(f + g)` to `D(f(f + g)) ⊕ D(g(f + g))` for all `f, g` in `R`, then
`H^q_étale(Spec R, F) = 0` for all `q > 0`. -/
@[stacks 0GY0] #check
  (AlgebraicGeometry.Scheme.etaleCohomology_isZero_of_h1Kernel_on_basicOpens :
    ∀ {R : Type u} [CommRing R]
      [AlgebraicGeometry.Scheme.HasStrictlyHenselianStalks (Spec (.of R))]
      (F : Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u})
      [HasSheafify (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u})]
      (h_kernel : AlgebraicGeometry.Scheme.etaleH1Kernel_basicOpen_add F),
      ∀ q : ℕ, 0 < q →
        IsZero ((Sheaf.functorH (Spec (.of R)).smallEtaleTopology q).obj F))
