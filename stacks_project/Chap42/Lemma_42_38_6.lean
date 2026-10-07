module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.Gysin

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ChernClassCap

/- Lemma 42.38.6: Gysin pullback along the zero-scheme inclusion of a section
of an invertible module commutes with the `j`th Chern-class cap of a finite
locally free module. -/
@[stacks 0B7G] #check (AlgebraicGeometry.ChowGroup.ChernClassCap.gysin :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (E : X.left.Modules) (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    (k : ℤ) (α : RelativeChow δ X k)
    (a : CycleGroup X.left (X.hom.relativeDimensionFunction δ) k)
    (ha : @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance k a = α)
    (b : CycleGroup (Scheme.zeroScheme ℒ s)
      ((Scheme.zeroSchemeι ℒ s ≫ X.hom).relativeDimensionFunction δ) (k - 1))
    (hb : @chowClass (Scheme.zeroScheme ℒ s)
      (LocallyOfFiniteType.isLocallyNoetherian (Scheme.zeroSchemeι ℒ s ≫ X.hom))
      ((Scheme.zeroSchemeι ℒ s ≫ X.hom).relativeDimensionFunction δ) inferInstance
      (k - 1) b = ChowGroup.gysin δ X ℒ s k α)
    (cX : ChernClassCap δ X.hom E r k a)
    (cD : ChernClassCap δ (Scheme.zeroSchemeι ℒ s ≫ X.hom)
      ((Scheme.Modules.pullback (Scheme.zeroSchemeι ℒ s)).obj E) r (k - 1) b)
    (j : ℕ),
    @ChowGroup.reindex (Scheme.zeroScheme ℒ s)
        (LocallyOfFiniteType.isLocallyNoetherian (Scheme.zeroSchemeι ℒ s ≫ X.hom))
        ((Scheme.zeroSchemeι ℒ s ≫ X.hom).relativeDimensionFunction δ) inferInstance
        ((k - 1) - (j : ℤ)) ((k - (j : ℤ)) - 1)
        (ChernClassCap.gysinDegree k j) (cD.component j) =
      ChowGroup.gysin δ X ℒ s (k - (j : ℤ)) (cX.component j))

end AlgebraicGeometry.ChowGroup.ChernClassCap
