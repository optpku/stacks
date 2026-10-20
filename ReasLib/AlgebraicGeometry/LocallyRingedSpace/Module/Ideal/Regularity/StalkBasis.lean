/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Ideal.QuasiRegular
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity.Implications

/-!
# Extending bases of ideal-stalk fibers

A basis of the residue-field fiber of an ideal stalk can be represented by ideal sections on a
neighborhood.  Under a regularity condition on the ideal sheaf, the representing sections may
be chosen to generate the restricted ideal sheaf and to have the corresponding stalkwise
regularity.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}}

/-- The residue-field fiber of an ideal-sheaf stalk, namely `Iₓ / 𝔪ₓ Iₓ`. -/
noncomputable abbrev idealStalkFiber (I : IdealSubobject X) (x : X) :=
  RingedSpace.idealSheafStalkIdeal I x ⧸
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x) (RingedSpace.idealSheafStalkIdeal I x)))

/-- The canonical class in the residue-field fiber of an element of an ideal-sheaf stalk. -/
noncomputable abbrev idealStalkFiberMk (I : IdealSubobject X) (x : X) :
    RingedSpace.idealSheafStalkIdeal I x → idealStalkFiber I x :=
  Submodule.mkQ
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x) (RingedSpace.idealSheafStalkIdeal I x)))

/-- A basis of the residue-field fiber of a quasi-regular ideal stalk lifts locally to a
quasi-regular family of ideal sections with the prescribed germs that generates the ideal
sheaf. -/
@[stacks 067N]
theorem exists_quasiRegularSequence_of_stalk_basis
    (I : IdealSubobject X) (hI : RingedSpace.IsQuasiRegularIdealSheaf I)
    (x : X) {r : ℕ} (f : Fin r → RingedSpace.idealSheafStalkIdeal I x)
    (hf_basis : ∃ b : Module.Basis (Fin r)
        ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (idealStalkFiber I x),
      ∀ i, idealStalkFiberMk I x (f i) = b i) :
    ∃ (U : Opens X) (hxU : x ∈ U) (g : Fin r → I.toModule.val.obj (op U)),
      (∀ i,
        (RingedSpace.idealSheafStalkToRing I x).hom
          (TopCat.Presheaf.germ I.toModule.val.presheaf U x hxU (g i)) = f i) ∧
        RingedSpace.IsGeneratedByIdealSectionFamilyOn I U g ∧
        RingedSpace.SectionSequence.IsQuasiRegular
          (fun i ↦ RingedSpace.idealSectionToRingSection I U (g i)) := sorry

/-- A basis of the residue-field fiber of an `H₁`-regular ideal stalk lifts locally to an
`H₁`-regular family of ideal sections with the prescribed germs that generates the ideal
sheaf. -/
@[stacks 067N]
theorem exists_h1RegularSequence_of_stalk_basis
    (I : IdealSubobject X) (hI : RingedSpace.IsH1RegularIdealSheaf I)
    (x : X) {r : ℕ} (f : Fin r → RingedSpace.idealSheafStalkIdeal I x)
    (hf_basis : ∃ b : Module.Basis (Fin r)
        ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (idealStalkFiber I x),
      ∀ i, idealStalkFiberMk I x (f i) = b i) :
    ∃ (U : Opens X) (hxU : x ∈ U) (g : Fin r → I.toModule.val.obj (op U)),
      (∀ i,
        (RingedSpace.idealSheafStalkToRing I x).hom
          (TopCat.Presheaf.germ I.toModule.val.presheaf U x hxU (g i)) = f i) ∧
        RingedSpace.IsGeneratedByIdealSectionFamilyOn I U g ∧
        RingedSpace.SectionSequence.IsH1Regular
          (fun i ↦ RingedSpace.idealSectionToRingSection I U (g i)) := sorry

/-- A basis of the residue-field fiber of a Koszul-regular ideal stalk lifts locally to a
Koszul-regular family of ideal sections with the prescribed germs that generates the ideal
sheaf. -/
@[stacks 067N]
theorem exists_koszulRegularSequence_of_stalk_basis
    (I : IdealSubobject X) (hI : RingedSpace.IsKoszulRegularIdealSheaf I)
    (x : X) {r : ℕ} (f : Fin r → RingedSpace.idealSheafStalkIdeal I x)
    (hf_basis : ∃ b : Module.Basis (Fin r)
        ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (idealStalkFiber I x),
      ∀ i, idealStalkFiberMk I x (f i) = b i) :
    ∃ (U : Opens X) (hxU : x ∈ U) (g : Fin r → I.toModule.val.obj (op U)),
      (∀ i,
        (RingedSpace.idealSheafStalkToRing I x).hom
          (TopCat.Presheaf.germ I.toModule.val.presheaf U x hxU (g i)) = f i) ∧
        RingedSpace.IsGeneratedByIdealSectionFamilyOn I U g ∧
        RingedSpace.SectionSequence.IsKoszulRegular
          (fun i ↦ RingedSpace.idealSectionToRingSection I U (g i)) := sorry

end AlgebraicGeometry.LocallyRingedSpace
