module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Regularity.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCheckRecall

@[expose] public section

open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The ideal of structure-sheaf sections represented by an ideal subobject over an open. -/
noncomputable abbrev idealSheafSectionIdeal {X : Scheme.{u}}
    (I : Scheme.IdealSubobject X) (U : X.Opens) :=
  SheafOfModules.RingedSite.IdealSheaf.sections I (op U)

end AlgebraicGeometry

/- Lemma 31.20.7 (1): an ideal sheaf is regular if and only if every point of its quotient
support has an affine neighborhood on which ideal sections generate the sheaf and their images
generate the section ideal as a regular sequence. -/
@[stacks 063G] #check
  (AlgebraicGeometry.Scheme.IdealSubobject.isRegular_iff_exists_affine_regularSequence :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : AlgebraicGeometry.Scheme.IdealSubobject X),
      AlgebraicGeometry.RingedSpace.IsRegularIdealSheaf I ↔
        ∀ x : X, x ∈ AlgebraicGeometry.RingedSpace.idealQuotientSupport I →
          ∃ U : X.affineOpens, ∃ _ : x ∈ (U : X.Opens), ∃ r : ℕ,
            ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
              RingTheory.Sequence.IsRegular
                  (X.presheaf.obj (op (U : X.Opens)))
                  (List.ofFn (fun i ↦
                    AlgebraicGeometry.RingedSpace.idealSectionToRingSection
                      I (U : X.Opens) (f i))) ∧
                AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn
                    I (U : X.Opens) f ∧
                  SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                    Ideal.span (Set.range fun i ↦
                      AlgebraicGeometry.RingedSpace.idealSectionToRingSection
                        I (U : X.Opens) (f i)))

/- Lemma 31.20.7 (2): an ideal sheaf is Koszul-regular if and only if every point of its quotient
support has an affine neighborhood on which ideal sections generate the sheaf and their images
generate the section ideal as a Koszul-regular sequence. -/
@[stacks 063G] #check
  (AlgebraicGeometry.Scheme.IdealSubobject.isKoszulRegular_iff_exists_affine_koszulRegularSequence :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : AlgebraicGeometry.Scheme.IdealSubobject X),
      AlgebraicGeometry.RingedSpace.IsKoszulRegularIdealSheaf I ↔
        ∀ x : X, x ∈ AlgebraicGeometry.RingedSpace.idealQuotientSupport I →
          ∃ U : X.affineOpens, ∃ _ : x ∈ (U : X.Opens), ∃ r : ℕ,
            ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
              RingTheory.Sequence.IsKoszulRegularSequence
                  (fun i ↦ AlgebraicGeometry.RingedSpace.idealSectionToRingSection
                    I (U : X.Opens) (f i)) ∧
                AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn
                    I (U : X.Opens) f ∧
                  SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                    Ideal.span (Set.range fun i ↦
                      AlgebraicGeometry.RingedSpace.idealSectionToRingSection
                        I (U : X.Opens) (f i)))

/- Lemma 31.20.7 (3): an ideal sheaf is `H₁`-regular if and only if every point of its quotient
support has an affine neighborhood on which ideal sections generate the sheaf and their images
generate the section ideal as an `H₁`-regular sequence. -/
@[stacks 063G] #check
  (AlgebraicGeometry.Scheme.IdealSubobject.isH1Regular_iff_exists_affine_h1RegularSequence :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : AlgebraicGeometry.Scheme.IdealSubobject X),
      AlgebraicGeometry.RingedSpace.IsH1RegularIdealSheaf I ↔
        ∀ x : X, x ∈ AlgebraicGeometry.RingedSpace.idealQuotientSupport I →
          ∃ U : X.affineOpens, ∃ _ : x ∈ (U : X.Opens), ∃ r : ℕ,
            ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
              RingTheory.Sequence.IsH1RegularSequence
                  (fun i ↦ AlgebraicGeometry.RingedSpace.idealSectionToRingSection
                    I (U : X.Opens) (f i)) ∧
                AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn
                    I (U : X.Opens) f ∧
                  SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                    Ideal.span (Set.range fun i ↦
                      AlgebraicGeometry.RingedSpace.idealSectionToRingSection
                        I (U : X.Opens) (f i)))

/- Lemma 31.20.7 (4): an ideal sheaf is quasi-regular if and only if every point of its quotient
support has an affine neighborhood on which ideal sections generate the sheaf and their images
generate the section ideal as a quasi-regular sequence. -/
@[stacks 063G] #check
  (AlgebraicGeometry.Scheme.IdealSubobject.isQuasiRegular_iff_exists_affine_quasiRegularSequence :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : AlgebraicGeometry.Scheme.IdealSubobject X),
      AlgebraicGeometry.RingedSpace.IsQuasiRegularIdealSheaf I ↔
        ∀ x : X, x ∈ AlgebraicGeometry.RingedSpace.idealQuotientSupport I →
          ∃ U : X.affineOpens, ∃ _ : x ∈ (U : X.Opens), ∃ r : ℕ,
            ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
              RingTheory.Sequence.IsQuasiRegular
                  (X.presheaf.obj (op (U : X.Opens)))
                  (List.ofFn (fun i ↦
                    AlgebraicGeometry.RingedSpace.idealSectionToRingSection
                      I (U : X.Opens) (f i))) ∧
                AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn
                    I (U : X.Opens) f ∧
                  SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                    Ideal.span (Set.range fun i ↦
                      AlgebraicGeometry.RingedSpace.idealSectionToRingSection
                        I (U : X.Opens) (f i)))
