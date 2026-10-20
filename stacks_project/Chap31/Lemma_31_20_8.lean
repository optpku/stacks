module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Regularity.Noetherian
import StacksCheckRecall

@[expose] public section

open Opposite

noncomputable section

universe u

/- Lemma 31.20.8: for a quasi-coherent ideal subobject on a locally Noetherian scheme and a
point in its quotient support, the four stalk-generation conditions, the four affine
presentations, and the four neighborhood regularity conditions are equivalent. -/
@[stacks 063I] #check
  (AlgebraicGeometry.Scheme.IdealSubobject.regularityAt_tfae :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (I : AlgebraicGeometry.Scheme.IdealSubobject X) [I.toModule.IsQuasicoherent]
      (x : X) (_ : x ∈ AlgebraicGeometry.RingedSpace.idealQuotientSupport I),
      List.TFAE [
        (∃ r : ℕ, ∃ f : Fin r → X.presheaf.stalk x,
          RingTheory.Sequence.IsRegular (X.presheaf.stalk x) (List.ofFn f) ∧
            AlgebraicGeometry.RingedSpace.idealSheafStalkIdeal I x =
              Ideal.span (Set.range f)),
        (∃ r : ℕ, ∃ f : Fin r → X.presheaf.stalk x,
          RingTheory.Sequence.IsKoszulRegularSequence f ∧
            AlgebraicGeometry.RingedSpace.idealSheafStalkIdeal I x =
              Ideal.span (Set.range f)),
        (∃ r : ℕ, ∃ f : Fin r → X.presheaf.stalk x,
          RingTheory.Sequence.IsH1RegularSequence f ∧
            AlgebraicGeometry.RingedSpace.idealSheafStalkIdeal I x =
              Ideal.span (Set.range f)),
        (∃ r : ℕ, ∃ f : Fin r → X.presheaf.stalk x,
          RingTheory.Sequence.IsQuasiRegular (X.presheaf.stalk x) (List.ofFn f) ∧
            AlgebraicGeometry.RingedSpace.idealSheafStalkIdeal I x =
              Ideal.span (Set.range f)),
        (∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens), ∃ r : ℕ,
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
                      I (U : X.Opens) (f i))),
        (∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens), ∃ r : ℕ,
          ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
            RingTheory.Sequence.IsKoszulRegularSequence
                (fun i ↦ AlgebraicGeometry.RingedSpace.idealSectionToRingSection
                  I (U : X.Opens) (f i)) ∧
              AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn
                  I (U : X.Opens) f ∧
                SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                  Ideal.span (Set.range fun i ↦
                    AlgebraicGeometry.RingedSpace.idealSectionToRingSection
                      I (U : X.Opens) (f i))),
        (∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens), ∃ r : ℕ,
          ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
            RingTheory.Sequence.IsH1RegularSequence
                (fun i ↦ AlgebraicGeometry.RingedSpace.idealSectionToRingSection
                  I (U : X.Opens) (f i)) ∧
              AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn
                  I (U : X.Opens) f ∧
                SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                  Ideal.span (Set.range fun i ↦
                    AlgebraicGeometry.RingedSpace.idealSectionToRingSection
                      I (U : X.Opens) (f i))),
        (∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens), ∃ r : ℕ,
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
                      I (U : X.Opens) (f i))),
        (∃ (U : X.Opens) (_ : x ∈ U) (r : ℕ)
            (f : Fin r → I.toModule.val.obj (op U)),
          AlgebraicGeometry.RingedSpace.SectionSequence.IsRegular
              (fun i ↦ AlgebraicGeometry.RingedSpace.idealSectionToRingSection I U (f i)) ∧
            AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn I U f),
        (∃ (U : X.Opens) (_ : x ∈ U) (r : ℕ)
            (f : Fin r → I.toModule.val.obj (op U)),
          AlgebraicGeometry.RingedSpace.SectionSequence.IsKoszulRegular
              (fun i ↦ AlgebraicGeometry.RingedSpace.idealSectionToRingSection I U (f i)) ∧
            AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn I U f),
        (∃ (U : X.Opens) (_ : x ∈ U) (r : ℕ)
            (f : Fin r → I.toModule.val.obj (op U)),
          AlgebraicGeometry.RingedSpace.SectionSequence.IsH1Regular
              (fun i ↦ AlgebraicGeometry.RingedSpace.idealSectionToRingSection I U (f i)) ∧
            AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn I U f),
        (∃ (U : X.Opens) (_ : x ∈ U) (r : ℕ)
            (f : Fin r → I.toModule.val.obj (op U)),
          AlgebraicGeometry.RingedSpace.SectionSequence.IsQuasiRegular
              (fun i ↦ AlgebraicGeometry.RingedSpace.idealSectionToRingSection I U (f i)) ∧
            AlgebraicGeometry.RingedSpace.IsGeneratedByIdealSectionFamilyOn I U f)
      ])

/- The global consequence identifies all four regularity conditions for an ideal subobject on
a locally Noetherian scheme. -/
#check
  (AlgebraicGeometry.Scheme.IdealSubobject.regularity_tfae :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (I : AlgebraicGeometry.Scheme.IdealSubobject X),
      List.TFAE [
        AlgebraicGeometry.RingedSpace.IsRegularIdealSheaf I,
        AlgebraicGeometry.RingedSpace.IsKoszulRegularIdealSheaf I,
        AlgebraicGeometry.RingedSpace.IsH1RegularIdealSheaf I,
        AlgebraicGeometry.RingedSpace.IsQuasiRegularIdealSheaf I
      ])
