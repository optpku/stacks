module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.ClosedImmersion.InternalHom.Coherent

@[expose] public section

open CategoryTheory
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 48.9.6: for a closed immersion `i : Z ⟶ X` with `X` locally Noetherian,
derived internal Hom from `𝒪_Z` sends bounded-below complexes with coherent cohomology
on `X` to bounded-below complexes with coherent cohomology on `Z`. -/
@[stacks 0A79] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.closedImmersionInternalHomPlus_coherent :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsLocallyNoetherian X] [IsClosedImmersion i]
      (K : D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]),
      DerivedCategory.Plus.cohomologyIn
        (SheafOfModules.isCoherent Z.toRingedSpace.ringCatSheaf)
        (((coherentPlusInclusion X ⋙ closedImmersionInternalHomPlus i) ⋙
          (DerivedCategory.Plus.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty Z.toRingedSpace)).ι).obj K))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.closedImmersionInternalHomCoherentPlus :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsLocallyNoetherian X] [IsClosedImmersion i],
      D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] ⥤
        D⁺[SheafOfModules.isCoherent Z.toRingedSpace.ringCatSheaf])

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.closedImmersionInternalHomCoherentPlus_obj_obj :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsLocallyNoetherian X] [IsClosedImmersion i]
      (K : D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]),
      ((closedImmersionInternalHomCoherentPlus i).obj K).obj =
        ((closedImmersionInternalHomPlus i).obj ((coherentPlusInclusion X).obj K)).obj)

end AlgebraicGeometry.Scheme.DerivedQCoh
