/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Underlying
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Pushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- Near a geometrically reduced fibre of a proper, flat, finitely presented morphism,
the derived pushforward of the structure sheaf decomposes as its finite étale degree-zero
algebra and a perfect summand of Tor amplitude in `[1, ∞)`. -/
theorem exists_local_finiteEtale_decomposition
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (s : S) [GeometricallyReduced (f.fiberToSpecResidueField s)] :
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
                      (Scheme.QcAlgebraUnder.underlyingModule U.toScheme A)) ⊞ P) := sorry

/-- For a proper smooth family with nonempty fibres, the pushforward of the
structure sheaf is represented by a finite étale relative spectrum. -/
theorem pushforwardStructureSheaf_finiteEtale
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
    [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) :
    let A := Scheme.pushforwardStructureSheafQcAlgebra f
    ∃ T : Scheme.RelativeSpectrumOver A,
      Scheme.IsRelativeSpectrumOver T ∧ IsFinite T.π ∧ Etale T.π := sorry

/-- For a proper smooth family with nonempty fibres, the derived pushforward
of the structure sheaf locally splits into its degree-zero algebra and a
perfect summand of Tor amplitude in `[1, ∞)`. -/
theorem exists_local_structureSheafPushforward_decomposition_of_smooth
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
    [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) (s : S) :
    ∃ U : S.Opens, s ∈ U ∧
      let g := f ∣_ U
      let A := Scheme.pushforwardStructureSheafQcAlgebra g
      ∃ P : RingedSpace.ModuleDerived U.toScheme.toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect P ∧
          RingedSpace.HasTorAmplitudeGE P 1 ∧
            IsIsomorphic
              ((RingedSpace.moduleDerivedPushforward g.toShHom).obj
                ((DerivedCategory.singleFunctor (f ⁻¹ᵁ U).toScheme.Modules 0).obj
                  (SheafOfModules.unit
                    (f ⁻¹ᵁ U).toScheme.toRingedSpace.ringCatSheaf)))
              (((DerivedCategory.singleFunctor U.toScheme.Modules 0).obj
                (Scheme.QcAlgebraUnder.underlyingModule U.toScheme A)) ⊞ P) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
