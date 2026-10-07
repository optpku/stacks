module

public import ReasLib.AlgebraicGeometry.ChowGroup.Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 42.19.3: for an open subscheme and its reduced closed complement, the Chow localization
complex is exact at the ambient scheme and restriction to the open subscheme is surjective. -/
@[stacks 02RX] #check (AlgebraicGeometry.ChowGroup.Localization.exact :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (U : X.Opens) (k : ℤ),
    (ChowGroup.Localization.complex p δ U k).Exact ∧
      Epi (ChowGroup.Localization.complex p δ U k).g)

end AlgebraicGeometry
