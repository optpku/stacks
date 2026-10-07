module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Regularity.Affine
public import ReasLib.RingTheory.Sequence.Regularity.Localization
public import ReasLib.RingTheory.Sequence.QuasiRegular.MaximalIdeal

/-!
# Regular ideal subobjects on locally Noetherian schemes

For a quasi-coherent ideal subobject on a locally Noetherian scheme, generation by regular,
Koszul-regular, `H₁`-regular, and quasi-regular sequences can be compared at a stalk, on an
affine neighborhood, and on an arbitrary open neighborhood.
-/

@[expose] public section

open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSubobject

variable {X : Scheme.{u}}

/-- At a point in the quotient support of a quasi-coherent ideal subobject on a locally
Noetherian scheme, the four stalk-generation conditions, their affine-neighborhood
presentations, and the corresponding four neighborhood regularity conditions are equivalent. -/
theorem regularityAt_tfae [IsLocallyNoetherian X]
    (I : Scheme.IdealSubobject X) [I.toModule.IsQuasicoherent]
    (x : X) (hx : x ∈ RingedSpace.idealQuotientSupport I) :
    List.TFAE [
      (∃ r : ℕ, ∃ f : Fin r → X.presheaf.stalk x,
        RingTheory.Sequence.IsRegular (X.presheaf.stalk x) (List.ofFn f) ∧
          RingedSpace.idealSheafStalkIdeal I x = Ideal.span (Set.range f)),
      (∃ r : ℕ, ∃ f : Fin r → X.presheaf.stalk x,
        RingTheory.Sequence.IsKoszulRegularSequence f ∧
          RingedSpace.idealSheafStalkIdeal I x = Ideal.span (Set.range f)),
      (∃ r : ℕ, ∃ f : Fin r → X.presheaf.stalk x,
        RingTheory.Sequence.IsH1RegularSequence f ∧
          RingedSpace.idealSheafStalkIdeal I x = Ideal.span (Set.range f)),
      (∃ r : ℕ, ∃ f : Fin r → X.presheaf.stalk x,
        RingTheory.Sequence.IsQuasiRegular (X.presheaf.stalk x) (List.ofFn f) ∧
          RingedSpace.idealSheafStalkIdeal I x = Ideal.span (Set.range f)),
      (∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens), ∃ r : ℕ,
        ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
          RingTheory.Sequence.IsRegular
              (X.presheaf.obj (op (U : X.Opens)))
              (List.ofFn (fun i ↦
                RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i))) ∧
            RingedSpace.IsGeneratedByIdealSectionFamilyOn I (U : X.Opens) f ∧
              SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                Ideal.span (Set.range fun i ↦
                  RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i))),
      (∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens), ∃ r : ℕ,
        ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
          RingTheory.Sequence.IsKoszulRegularSequence
              (fun i ↦ RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i)) ∧
            RingedSpace.IsGeneratedByIdealSectionFamilyOn I (U : X.Opens) f ∧
              SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                Ideal.span (Set.range fun i ↦
                  RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i))),
      (∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens), ∃ r : ℕ,
        ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
          RingTheory.Sequence.IsH1RegularSequence
              (fun i ↦ RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i)) ∧
            RingedSpace.IsGeneratedByIdealSectionFamilyOn I (U : X.Opens) f ∧
              SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                Ideal.span (Set.range fun i ↦
                  RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i))),
      (∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens), ∃ r : ℕ,
        ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
          RingTheory.Sequence.IsQuasiRegular
              (X.presheaf.obj (op (U : X.Opens)))
              (List.ofFn (fun i ↦
                RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i))) ∧
            RingedSpace.IsGeneratedByIdealSectionFamilyOn I (U : X.Opens) f ∧
              SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                Ideal.span (Set.range fun i ↦
                  RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i))),
      (∃ (U : X.Opens) (_ : x ∈ U) (r : ℕ)
          (f : Fin r → I.toModule.val.obj (op U)),
        RingedSpace.SectionSequence.IsRegular
            (fun i ↦ RingedSpace.idealSectionToRingSection I U (f i)) ∧
          RingedSpace.IsGeneratedByIdealSectionFamilyOn I U f),
      (∃ (U : X.Opens) (_ : x ∈ U) (r : ℕ)
          (f : Fin r → I.toModule.val.obj (op U)),
        RingedSpace.SectionSequence.IsKoszulRegular
            (fun i ↦ RingedSpace.idealSectionToRingSection I U (f i)) ∧
          RingedSpace.IsGeneratedByIdealSectionFamilyOn I U f),
      (∃ (U : X.Opens) (_ : x ∈ U) (r : ℕ)
          (f : Fin r → I.toModule.val.obj (op U)),
        RingedSpace.SectionSequence.IsH1Regular
            (fun i ↦ RingedSpace.idealSectionToRingSection I U (f i)) ∧
          RingedSpace.IsGeneratedByIdealSectionFamilyOn I U f),
      (∃ (U : X.Opens) (_ : x ∈ U) (r : ℕ)
          (f : Fin r → I.toModule.val.obj (op U)),
        RingedSpace.SectionSequence.IsQuasiRegular
            (fun i ↦ RingedSpace.idealSectionToRingSection I U (f i)) ∧
          RingedSpace.IsGeneratedByIdealSectionFamilyOn I U f)
    ] := sorry

/-- On a locally Noetherian scheme, regular, Koszul-regular, `H₁`-regular, and quasi-regular
ideal subobjects satisfy equivalent local generation conditions. -/
theorem regularity_tfae [IsLocallyNoetherian X] (I : Scheme.IdealSubobject X) :
    List.TFAE [
      RingedSpace.IsRegularIdealSheaf I,
      RingedSpace.IsKoszulRegularIdealSheaf I,
      RingedSpace.IsH1RegularIdealSheaf I,
      RingedSpace.IsQuasiRegularIdealSheaf I
    ] := sorry

end AlgebraicGeometry.Scheme.IdealSubobject
