/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Construction

/-!
# Relative spectra of pushed-forward structure sheaves

This file constructs the canonical map from a scheme to an explicit relative-spectrum model
of the pushforward of its structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Opposite
open RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- The canonical morphism from `X` to an explicit relative-spectrum model of `f_* 𝒪_X`. -/
noncomputable def pushforwardStructureSheafRelativeSpectrumHom
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (P : RelativeSpectrumOver (pushforwardStructureSheafQcAlgebra f))
    [IsRelativeSpectrumOver P] :
    X ⟶ relativeSpec P :=
  (IsRelativeSpectrumOver.isRepresentedBy (P := P)).representableBy.homEquiv.symm
    (⟨f, 𝟙 (Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom))⟩ :
      relativeSpectrumPair (pushforwardStructureSheafQcAlgebra f) X)

/-- The canonical morphism to the relative spectrum of `f_* 𝒪_X` lies over `S`. -/
theorem pushforwardStructureSheafRelativeSpectrumHom_over
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (P : RelativeSpectrumOver (pushforwardStructureSheafQcAlgebra f))
    [IsRelativeSpectrumOver P] :
    pushforwardStructureSheafRelativeSpectrumHom f P ≫ relativeSpecπ P = f := sorry

/-- The preimage of an open under `f` maps into its preimage under the structural morphism of
the relative-spectrum model. -/
theorem pushforwardStructureSheafRelativeSpectrumHom_restrict_le
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (P : RelativeSpectrumOver (pushforwardStructureSheafQcAlgebra f))
    [IsRelativeSpectrumOver P] (U : S.Opens) :
    f ⁻¹ᵁ U ≤
      pushforwardStructureSheafRelativeSpectrumHom f P ⁻¹ᵁ (relativeSpecπ P ⁻¹ᵁ U) := sorry

/-- On every affine open of the base, the restricted canonical morphism agrees with the
canonical morphism to the spectrum of sections under any compatible affine realization of the
chosen relative-spectrum model. -/
theorem pushforwardStructureSheafRelativeSpectrumHom_restrict_eq_toSpec
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (P : RelativeSpectrumOver (pushforwardStructureSheafQcAlgebra f))
    [IsRelativeSpectrumOver P]
    (U : S.Opens) (hU : IsAffineOpen U)
    (iSpec : ∀ (V : S.Opens) (hV : IsAffineOpen V),
      ((relativeSpecπ P ⁻¹ᵁ V).toScheme ≅
        Spec (qcAlgebraSectionRing (pushforwardStructureSheafQcAlgebra f) V)))
    (hiSpec :
      (∀ (V : S.Opens) (hV : IsAffineOpen V),
        (iSpec V hV).hom ≫
            Spec.map (qcAlgebraStructureMap (pushforwardStructureSheafQcAlgebra f) V) ≫
            hV.isoSpec.inv =
          relativeSpecπ P ∣_ V) ∧
      ∀ {V V' : S.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V ≤ V'),
        (iSpec V hV).inv ≫
            (relativeSpec P).homOfLE ((relativeSpecπ P).preimage_mono h) ≫
            (iSpec V' hV').hom =
          Spec.map (qcAlgebraSectionRestrict (pushforwardStructureSheafQcAlgebra f) h)) :
    (pushforwardStructureSheafRelativeSpectrumHom f P).resLE
        (relativeSpecπ P ⁻¹ᵁ U) (f ⁻¹ᵁ U)
        (pushforwardStructureSheafRelativeSpectrumHom_restrict_le f P U) ≫
      (iSpec U hU).hom =
        (f ⁻¹ᵁ U).toSpecΓ := sorry

/-- On every affine open of the base, the chosen relative-spectrum model is isomorphic over
that open to the spectrum of the corresponding section ring, and under this isomorphism the
restricted canonical morphism is the canonical morphism to the spectrum of global sections. -/
theorem pushforwardStructureSheafRelativeSpectrumHom_restrict_exists_iso_toSpec
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (P : RelativeSpectrumOver (pushforwardStructureSheafQcAlgebra f))
    [IsRelativeSpectrumOver P]
    (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ iSpec : ((relativeSpecπ P ⁻¹ᵁ U).toScheme ≅
        Spec (qcAlgebraSectionRing (pushforwardStructureSheafQcAlgebra f) U)),
      (iSpec.hom ≫
            Spec.map (qcAlgebraStructureMap (pushforwardStructureSheafQcAlgebra f) U) ≫
            hU.isoSpec.inv =
          relativeSpecπ P ∣_ U) ∧
        (pushforwardStructureSheafRelativeSpectrumHom f P).resLE
              (relativeSpecπ P ⁻¹ᵁ U) (f ⁻¹ᵁ U)
              (pushforwardStructureSheafRelativeSpectrumHom_restrict_le f P U) ≫
            iSpec.hom =
          (f ⁻¹ᵁ U).toSpecΓ := sorry

end AlgebraicGeometry.Scheme
