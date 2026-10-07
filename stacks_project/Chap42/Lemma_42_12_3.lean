module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.CycleGroup.ClosedCover

open CategoryTheory

universe u

namespace AlgebraicGeometry.CycleGroup.ClosedCover

/- Lemma 42.12.3: if two closed subschemes cover `X` set-theoretically, then for every
`k : ℤ` their signed intersection pushforward and sum of ambient pushforwards form an exact
sequence ending in zero. -/
@[stacks 0F92]
#check (AlgebraicGeometry.CycleGroup.ClosedCover.exact :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
      [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
      (Z₁ Z₂ : X.IdealSheafData) (_ : Z₁.support ⊔ Z₂.support = ⊤) (k : ℤ),
    (complex p δ Z₁ Z₂ k).Exact ∧ Epi (complex p δ Z₁ Z₂ k).g)

end AlgebraicGeometry.CycleGroup.ClosedCover
