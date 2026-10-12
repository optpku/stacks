/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Regularity

/-!
# Affine criteria for regular ideal subobjects

Regularity conditions on an ideal subobject of a scheme can be detected on affine
neighborhoods of the support of its quotient.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSubobject

variable {X : Scheme.{u}}

/-- An ideal subobject is regular exactly when, near every point of its quotient support, it is
generated on an affine open by ideal sections whose images form a regular sequence and generate
the ideal of sections. -/
theorem isRegular_iff_exists_affine_regularSequence (I : Scheme.IdealSubobject X) :
    RingedSpace.IsRegularIdealSheaf I ↔
      ∀ x : X, x ∈ RingedSpace.idealQuotientSupport I →
        ∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens), ∃ r : ℕ,
          ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
            RingTheory.Sequence.IsRegular
                (X.presheaf.obj (op (U : X.Opens)))
                (List.ofFn (fun i ↦
                  RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i))) ∧
              RingedSpace.IsGeneratedByIdealSectionFamilyOn I (U : X.Opens) f ∧
                SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                  Ideal.span (Set.range fun i ↦
                    RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i)) := sorry

/-- An ideal subobject is Koszul-regular exactly when, near every point of its quotient support,
it is generated on an affine open by ideal sections whose images form a Koszul-regular sequence
and generate the ideal of sections. -/
theorem isKoszulRegular_iff_exists_affine_koszulRegularSequence
    (I : Scheme.IdealSubobject X) :
    RingedSpace.IsKoszulRegularIdealSheaf I ↔
      ∀ x : X, x ∈ RingedSpace.idealQuotientSupport I →
        ∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens), ∃ r : ℕ,
          ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
            RingTheory.Sequence.IsKoszulRegularSequence
                (fun i ↦
                  RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i)) ∧
              RingedSpace.IsGeneratedByIdealSectionFamilyOn I (U : X.Opens) f ∧
                SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                  Ideal.span (Set.range fun i ↦
                    RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i)) := sorry

/-- An ideal subobject is `H₁`-regular exactly when, near every point of its quotient support, it
is generated on an affine open by ideal sections whose images form an `H₁`-regular sequence and
generate the ideal of sections. -/
theorem isH1Regular_iff_exists_affine_h1RegularSequence (I : Scheme.IdealSubobject X) :
    RingedSpace.IsH1RegularIdealSheaf I ↔
      ∀ x : X, x ∈ RingedSpace.idealQuotientSupport I →
        ∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens), ∃ r : ℕ,
          ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
            RingTheory.Sequence.IsH1RegularSequence
                (fun i ↦
                  RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i)) ∧
              RingedSpace.IsGeneratedByIdealSectionFamilyOn I (U : X.Opens) f ∧
                SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                  Ideal.span (Set.range fun i ↦
                    RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i)) := sorry

/-- An ideal subobject is quasi-regular exactly when, near every point of its quotient support,
it is generated on an affine open by ideal sections whose images form a quasi-regular sequence
and generate the ideal of sections. -/
theorem isQuasiRegular_iff_exists_affine_quasiRegularSequence
    (I : Scheme.IdealSubobject X) :
    RingedSpace.IsQuasiRegularIdealSheaf I ↔
      ∀ x : X, x ∈ RingedSpace.idealQuotientSupport I →
        ∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens), ∃ r : ℕ,
          ∃ f : Fin r → I.toModule.val.obj (op (U : X.Opens)),
            RingTheory.Sequence.IsQuasiRegular
                (X.presheaf.obj (op (U : X.Opens)))
                (List.ofFn (fun i ↦
                  RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i))) ∧
              RingedSpace.IsGeneratedByIdealSectionFamilyOn I (U : X.Opens) f ∧
                SheafOfModules.RingedSite.IdealSheaf.sections I (op (U : X.Opens)) =
                  Ideal.span (Set.range fun i ↦
                    RingedSpace.idealSectionToRingSection I (U : X.Opens) (f i)) := sorry

end AlgebraicGeometry.Scheme.IdealSubobject
