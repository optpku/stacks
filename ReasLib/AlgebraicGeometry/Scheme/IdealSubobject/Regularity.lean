/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity.Implications
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Quasicoherent

/-!
# Regular ideal subobjects of schemes

Regularity conditions on an ideal subobject imply finiteness and quasi-coherence of its
represented module sheaf.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSubobject

variable {X : Scheme.{u}}

/-- A quasi-regular ideal subobject of a scheme is represented by a finite-type module sheaf. -/
@[instance]
theorem isFiniteType_of_isQuasiRegular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsQuasiRegularIdealSheaf I] : I.toModule.IsFiniteType := sorry

/-- A quasi-regular ideal subobject of a scheme is represented by a quasi-coherent module
sheaf. -/
@[instance]
theorem isQuasicoherent_of_isQuasiRegular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsQuasiRegularIdealSheaf I] : I.toModule.IsQuasicoherent := by
  letI : I.toModule.IsFiniteType := isFiniteType_of_isQuasiRegular I
  exact (isLocallyGeneratedBySections_iff_isQuasicoherent I).mp inferInstance

/-- An `H₁`-regular ideal subobject of a scheme is represented by a finite-type module sheaf. -/
@[instance]
theorem isFiniteType_of_isH1Regular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsH1RegularIdealSheaf I] : I.toModule.IsFiniteType := by
  letI : RingedSpace.IsQuasiRegularIdealSheaf I :=
    { locallyGeneratedByQuasiRegularSequence := by
        intro x hx
        have h := (inferInstance : RingedSpace.IsH1RegularIdealSheaf I)
          |>.locallyGeneratedByH1RegularSequence
        dsimp [RingedSpace.isLocallyGeneratedBySequencePredicate] at h
        obtain ⟨U, hxU, r, f, hf, hgen⟩ := h x hx
        exact ⟨U, hxU, r, f,
          RingedSpace.SectionSequence.IsH1Regular.isQuasiRegular hf, hgen⟩ }
  exact isFiniteType_of_isQuasiRegular I

/-- An `H₁`-regular ideal subobject of a scheme is represented by a quasi-coherent module
sheaf. -/
@[instance]
theorem isQuasicoherent_of_isH1Regular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsH1RegularIdealSheaf I] : I.toModule.IsQuasicoherent := by
  letI : I.toModule.IsFiniteType := isFiniteType_of_isH1Regular I
  exact (isLocallyGeneratedBySections_iff_isQuasicoherent I).mp inferInstance

/-- A Koszul-regular ideal subobject of a scheme is represented by a finite-type module sheaf. -/
@[instance]
theorem isFiniteType_of_isKoszulRegular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsKoszulRegularIdealSheaf I] : I.toModule.IsFiniteType := by
  letI : RingedSpace.IsQuasiRegularIdealSheaf I :=
    { locallyGeneratedByQuasiRegularSequence := by
        intro x hx
        have h := (inferInstance : RingedSpace.IsKoszulRegularIdealSheaf I)
          |>.locallyGeneratedByKoszulRegularSequence
        dsimp [RingedSpace.isLocallyGeneratedBySequencePredicate] at h
        obtain ⟨U, hxU, r, f, hf, hgen⟩ := h x hx
        exact ⟨U, hxU, r, f,
          RingedSpace.SectionSequence.IsH1Regular.isQuasiRegular
            (RingedSpace.SectionSequence.IsKoszulRegular.isH1Regular hf), hgen⟩ }
  exact isFiniteType_of_isQuasiRegular I

/-- A Koszul-regular ideal subobject of a scheme is represented by a quasi-coherent module
sheaf. -/
@[instance]
theorem isQuasicoherent_of_isKoszulRegular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsKoszulRegularIdealSheaf I] : I.toModule.IsQuasicoherent := by
  letI : I.toModule.IsFiniteType := isFiniteType_of_isKoszulRegular I
  exact (isLocallyGeneratedBySections_iff_isQuasicoherent I).mp inferInstance

/-- A regular ideal subobject of a scheme is represented by a finite-type module sheaf. -/
@[instance]
theorem isFiniteType_of_isRegular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsRegularIdealSheaf I] : I.toModule.IsFiniteType := by
  letI : RingedSpace.IsQuasiRegularIdealSheaf I :=
    { locallyGeneratedByQuasiRegularSequence := by
        intro x hx
        have h := (inferInstance : RingedSpace.IsRegularIdealSheaf I)
          |>.locallyGeneratedByRegularSequence
        dsimp [RingedSpace.isLocallyGeneratedBySequencePredicate] at h
        obtain ⟨U, hxU, r, f, hf, hgen⟩ := h x hx
        exact ⟨U, hxU, r, f,
          RingedSpace.SectionSequence.IsH1Regular.isQuasiRegular
            (RingedSpace.SectionSequence.IsKoszulRegular.isH1Regular
              (RingedSpace.SectionSequence.IsRegular.isKoszulRegular hf)), hgen⟩ }
  exact isFiniteType_of_isQuasiRegular I

/-- A regular ideal subobject of a scheme is represented by a quasi-coherent module sheaf. -/
@[instance]
theorem isQuasicoherent_of_isRegular (I : Scheme.IdealSubobject X)
    [RingedSpace.IsRegularIdealSheaf I] : I.toModule.IsQuasicoherent := by
  letI : I.toModule.IsFiniteType := isFiniteType_of_isRegular I
  exact (isLocallyGeneratedBySections_iff_isQuasicoherent I).mp inferInstance

end AlgebraicGeometry.Scheme.IdealSubobject
