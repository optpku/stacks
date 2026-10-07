module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 42.20.3: Proper pushforward sends rationally equivalent degree-`k` cycles
to rationally equivalent degree-`k` cycles. -/
@[stacks 02S2] #check (AlgebraicGeometry.RationalEquivalence.map_mem_boundaries_of_proper :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) [IsProper f.left] (k : ℤ),
      @AlgebraicGeometry.RationalEquivalence.boundaries X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance k ≤
        (@AlgebraicGeometry.RationalEquivalence.boundaries Y.left
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction δ) inferInstance k).comap
          (AlgebraicGeometry.CycleGroup.mapHom f.left
            (X.hom.relativeDimensionFunction δ)
            (Y.hom.relativeDimensionFunction δ) k))

end AlgebraicGeometry
