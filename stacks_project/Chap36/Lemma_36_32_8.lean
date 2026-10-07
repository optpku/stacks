module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.StructureSheaf.FiniteEtale

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

/- Lemma 36.32.8: near a point whose fibre is geometrically reduced, the derived
pushforward `Rf_*𝒪_X` decomposes as its finite étale degree-zero algebra and a perfect
summand of Tor amplitude in `[1, ∞)`. -/
@[stacks 0G7Y] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.exists_local_finiteEtale_decomposition :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      (s : S) [GeometricallyReduced (f.fiberToSpecResidueField s)],
      ∃ U : S.Opens, s ∈ U ∧
        let g := f ∣_ U
        let A := Scheme.pushforwardStructureSheafQcAlgebra g
        ∃ T : Scheme.RelativeSpectrumOver A,
          Scheme.IsRelativeSpectrumOver T ∧
            IsFinite T.π ∧ Etale T.π ∧
              ∃ P : RingedSpace.ModuleDerived U.toScheme.toRingedSpace,
                RingedSpace.ModuleDerived.IsPerfect P ∧
                  RingedSpace.HasTorAmplitudeGE P 1 ∧
                    IsIsomorphic
                      ((RingedSpace.moduleDerivedPushforward g.toShHom).obj
                        ((DerivedCategory.singleFunctor (f ⁻¹ᵁ U).toScheme.Modules 0).obj
                          (SheafOfModules.unit
                            (f ⁻¹ᵁ U).toScheme.toRingedSpace.ringCatSheaf)))
                      (((DerivedCategory.singleFunctor U.toScheme.Modules 0).obj
                        (Scheme.QcAlgebraUnder.underlyingModule U.toScheme A)) ⊞ P))
