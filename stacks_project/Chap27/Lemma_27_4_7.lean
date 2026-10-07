module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Pushforward
import StacksCheckRecall

/-!
# Lemma 27.4.7 compatibility entry point

The pushed-forward quasi-coherent algebra and its canonical morphism to an explicit
relative-spectrum model are owned by ReasLib.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry

/- The quasi-coherence assertion used to bundle the pushed-forward structure sheaf. -/
#check
  (AlgebraicGeometry.Scheme.pushforwardStructureSheaf_isQuasicoherent :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f],
      ((SheafOfModules.RingedSite.restrictionAlong
          (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)).obj
        (SheafOfModules.RingedSite.unitModule
          (Opens.grothendieckTopology S)
          ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf))).IsQuasicoherent)

/- The bundled quasi-coherent algebra `f_* 𝒪_X`. -/
#check
  (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f],
      S.QcAlgebraUnder)

/- The underlying algebra of the pushed-forward quasi-coherent algebra. -/
#check
  (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra_obj :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f],
      (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f).obj =
        CategoryTheory.Under.mk
          (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom))

/- Lemma 27.4.7: the canonical morphism from `X` to an explicit relative-spectrum model of
`f_* 𝒪_X`. -/
@[stacks 01LY] #check
  (AlgebraicGeometry.Scheme.pushforwardStructureSheafRelativeSpectrumHom :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver
        (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f))
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      X ⟶ AlgebraicGeometry.Scheme.relativeSpec P)

/- The canonical morphism lies over the base scheme. -/
#check
  (AlgebraicGeometry.Scheme.pushforwardStructureSheafRelativeSpectrumHom_over :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver
        (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f))
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      AlgebraicGeometry.Scheme.pushforwardStructureSheafRelativeSpectrumHom f P ≫
          AlgebraicGeometry.Scheme.relativeSpecπ P =
        f)

/- The containment needed to restrict the canonical morphism over an open of the base. -/
#check
  (AlgebraicGeometry.Scheme.pushforwardStructureSheafRelativeSpectrumHom_restrict_le :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver
        (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f))
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P] (U : S.Opens),
      f ⁻¹ᵁ U ≤
        AlgebraicGeometry.Scheme.pushforwardStructureSheafRelativeSpectrumHom f P ⁻¹ᵁ
          (AlgebraicGeometry.Scheme.relativeSpecπ P ⁻¹ᵁ U))

/- On an affine open, the restricted canonical morphism is the canonical morphism to the
spectrum of sections. -/
#check (AlgebraicGeometry.Scheme.pushforwardStructureSheafRelativeSpectrumHom_restrict_eq_toSpec :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver
        (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f))
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P]
      (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
      (iSpec : ∀ (V : S.Opens) (hV : AlgebraicGeometry.IsAffineOpen V),
        ((AlgebraicGeometry.Scheme.relativeSpecπ P ⁻¹ᵁ V).toScheme ≅
          AlgebraicGeometry.Spec
            (AlgebraicGeometry.Scheme.qcAlgebraSectionRing
              (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f) V)))
      (hiSpec :
        (∀ (V : S.Opens) (hV : AlgebraicGeometry.IsAffineOpen V),
          (iSpec V hV).hom ≫
              AlgebraicGeometry.Spec.map
                (AlgebraicGeometry.Scheme.qcAlgebraStructureMap
                  (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f) V) ≫
              hV.isoSpec.inv =
            AlgebraicGeometry.morphismRestrict
              (AlgebraicGeometry.Scheme.relativeSpecπ P) V) ∧
        ∀ {V V' : S.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
          (hV' : AlgebraicGeometry.IsAffineOpen V') (h : V ≤ V'),
          (iSpec V hV).inv ≫
              (AlgebraicGeometry.Scheme.relativeSpec P).homOfLE
                ((AlgebraicGeometry.Scheme.relativeSpecπ P).preimage_mono h) ≫
              (iSpec V' hV').hom =
            AlgebraicGeometry.Spec.map
              (AlgebraicGeometry.Scheme.qcAlgebraSectionRestrict
                (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f) h)),
      (AlgebraicGeometry.Scheme.pushforwardStructureSheafRelativeSpectrumHom f P).resLE
          (AlgebraicGeometry.Scheme.relativeSpecπ P ⁻¹ᵁ U) (f ⁻¹ᵁ U)
          (AlgebraicGeometry.Scheme.pushforwardStructureSheafRelativeSpectrumHom_restrict_le
            f P U) ≫
        (iSpec U hU).hom =
          (f ⁻¹ᵁ U).toSpecΓ)

/- On an affine open, some relative-spectrum identification carries the restricted canonical
morphism to the canonical morphism to the spectrum of sections. -/
#check
  (AlgebraicGeometry.Scheme.pushforwardStructureSheafRelativeSpectrumHom_restrict_exists_iso_toSpec :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver
        (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f))
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P]
      (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U),
      ∃ iSpec :
          ((AlgebraicGeometry.Scheme.relativeSpecπ P ⁻¹ᵁ U).toScheme ≅
            AlgebraicGeometry.Spec
              (AlgebraicGeometry.Scheme.qcAlgebraSectionRing
                (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f) U)),
        (iSpec.hom ≫
              AlgebraicGeometry.Spec.map
                (AlgebraicGeometry.Scheme.qcAlgebraStructureMap
                  (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f) U) ≫
              hU.isoSpec.inv =
            AlgebraicGeometry.morphismRestrict
              (AlgebraicGeometry.Scheme.relativeSpecπ P) U) ∧
          (AlgebraicGeometry.Scheme.pushforwardStructureSheafRelativeSpectrumHom f P).resLE
                (AlgebraicGeometry.Scheme.relativeSpecπ P ⁻¹ᵁ U) (f ⁻¹ᵁ U)
                (AlgebraicGeometry.Scheme.pushforwardStructureSheafRelativeSpectrumHom_restrict_le
                  f P U) ≫
              iSpec.hom =
            (f ⁻¹ᵁ U).toSpecΓ)
