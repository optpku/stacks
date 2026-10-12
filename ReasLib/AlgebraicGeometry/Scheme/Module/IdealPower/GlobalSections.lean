/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Torsion
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Kernel
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Sections
public import ReasLib.CategoryTheory.Functor.OfSequence.Colimit

/-!
# Ideal-power Hom colimits and sections on an open complement

This file constructs the global directed systems of morphisms out of powers of an ideal sheaf,
their canonical evaluation maps on the complement of the ideal support, and the corresponding
systems after quotienting by power torsion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The ideal subobject associated to the `n`th power of ideal-sheaf data. -/
noncomputable abbrev idealSheafPowerSubobject
    (I : X.IdealSheafData) (n : ℕ) :
    Subobject (SheafOfModules.unit X.ringCatSheaf) :=
  RingedSpace.Hom.kernelIdealSubobject (I ^ n).subschemeι.toShHom

/-- Ideal-power subobjects decrease as the exponent increases. -/
theorem idealSheafPowerSubobject_antitone (I : X.IdealSheafData)
    {m n : ℕ} (h : m ≤ n) :
    idealSheafPowerSubobject I n ≤ idealSheafPowerSubobject I m := sorry

/-- The module sheaf underlying the `n`th ideal-power subobject. -/
noncomputable abbrev idealSheafPowerModule
    (I : X.IdealSheafData) (n : ℕ) : X.Modules :=
  Subobject.underlying.obj (idealSheafPowerSubobject I n)

/-- Restriction along the inclusion `I^(n+1) ⊆ I^n`. -/
noncomputable def idealSheafPowerTransition (I : X.IdealSheafData) (n : ℕ) :
    idealSheafPowerModule I (n + 1) ⟶ idealSheafPowerModule I n :=
  Subobject.ofLE _ _ (idealSheafPowerSubobject_antitone I n.le_succ)

/-- The additive group of module-sheaf morphisms `I^n ⟶ ℱ`. -/
noncomputable abbrev idealSheafPowerHomStage
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (idealSheafPowerModule I n ⟶ ℱ)

/-- Precomposition with `I^(n+1) ⟶ I^n` gives the transition between Hom stages. -/
noncomputable def idealSheafPowerHomTransition
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealSheafPowerHomStage I ℱ n ⟶ idealSheafPowerHomStage I ℱ (n + 1) :=
  AddCommGrpCat.ofHom (Preadditive.leftComp ℱ (idealSheafPowerTransition I n))

/-- The sequential additive-group diagram `n ↦ Hom(I^n, ℱ)`. -/
noncomputable def idealSheafPowerHomDiagram
    (I : X.IdealSheafData) (ℱ : X.Modules) : ℕ ⥤ AddCommGrpCat.{u} :=
  Functor.ofSequence (idealSheafPowerHomTransition I ℱ)

/-- On the complement of the support, the inclusion of every ideal power into the structure
sheaf is an isomorphism on sections. -/
noncomputable instance idealSheafPowerSubobject_arrow_app_isIso
    (I : X.IdealSheafData) (n : ℕ) :
    IsIso ((idealSheafPowerSubobject I n).arrow.val.app (op I.openComplement)) := sorry

/-- Evaluation of a morphism `I^n ⟶ ℱ` at the canonical unit section on the complement. -/
noncomputable def idealSheafPowerHomToComplementSectionsStageMap
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealSheafPowerHomStage I ℱ n ⟶ Γ(ℱ, I.openComplement) :=
  AddCommGrpCat.ofHom
    { toFun := fun φ ↦
        φ.val.app (op I.openComplement)
          (inv ((idealSheafPowerSubobject I n).arrow.val.app (op I.openComplement))
            (1 : Γ(X, I.openComplement)))
      map_zero' := by rfl
      map_add' := by intro φ ψ; rfl }

/-- The stage evaluations commute with restriction along successive ideal powers. -/
theorem idealSheafPowerHomToComplementSectionsStageMap_naturality
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealSheafPowerHomTransition I ℱ n ≫
        idealSheafPowerHomToComplementSectionsStageMap I ℱ (n + 1) =
      idealSheafPowerHomToComplementSectionsStageMap I ℱ n := sorry

/-- The canonical additive map from `colim_n Hom(I^n, ℱ)` to sections of `ℱ` on the
complement of the ideal support. -/
noncomputable def idealSheafPowerHomColimitToComplementSections
    (I : X.IdealSheafData) (ℱ : X.Modules) :
    colimit (idealSheafPowerHomDiagram I ℱ) ⟶ Γ(ℱ, I.openComplement) :=
  Functor.ofSequence.colimitDesc
    (idealSheafPowerHomTransition I ℱ)
    (idealSheafPowerHomToComplementSectionsStageMap I ℱ)
    (idealSheafPowerHomToComplementSectionsStageMap_naturality I ℱ)

/-- The global comparison restricts to its defining evaluation on every Hom stage. -/
@[reassoc]
theorem idealSheafPowerHomColimitToComplementSections_ι
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    colimit.ι (idealSheafPowerHomDiagram I ℱ) n ≫
        idealSheafPowerHomColimitToComplementSections I ℱ =
      idealSheafPowerHomToComplementSectionsStageMap I ℱ n := sorry

/-- Restricting the global comparison to the intersection with an affine open agrees with
restricting its defining stage evaluation. -/
theorem idealSheafPowerHomColimitToComplementSections_restrict_affine
    (I : X.IdealSheafData) (ℱ : X.Modules) (V : X.affineOpens) (n : ℕ) :
    colimit.ι (idealSheafPowerHomDiagram I ℱ) n ≫
        idealSheafPowerHomColimitToComplementSections I ℱ ≫
          ℱ.presheaf.map (homOfLE (inf_le_left :
            I.openComplement ⊓ (V : X.Opens) ≤ I.openComplement)).op =
      idealSheafPowerHomToComplementSectionsStageMap I ℱ n ≫
        ℱ.presheaf.map (homOfLE (inf_le_left :
          I.openComplement ⊓ (V : X.Opens) ≤ I.openComplement)).op := sorry

/-- For a quasi-compact scheme, a finite-type ideal sheaf, and a quasi-coherent module sheaf,
the canonical ideal-power Hom comparison to sections on the support complement is injective. -/
theorem idealSheafPowerHomColimitToComplementSections_injective
    [CompactSpace X.carrier] (I : X.IdealSheafData) (hI : I.IsFiniteType)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    Function.Injective
      (idealSheafPowerHomColimitToComplementSections I ℱ).hom := sorry

/-- The subsheaf of sections of `ℱ` annihilated by the `n`th tensor power of `I`. -/
noncomputable abbrev idealPowerTorsion
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) : X.Modules :=
  SheafOfModules.RingedSite.IdealSheaf.powerTorsion.{u, u}
    (idealSheafPowerSubobject I 1) ℱ n

/-- The canonical inclusion of the subsheaf annihilated by `I^n` into `ℱ`. -/
noncomputable abbrev idealPowerTorsionι
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealPowerTorsion I ℱ n ⟶ ℱ :=
  SheafOfModules.RingedSite.IdealSheaf.powerTorsionι.{u, u}
    (idealSheafPowerSubobject I 1) ℱ n

/-- Sections annihilated by `I^n` are also annihilated by `I^(n+1)`. -/
theorem idealPowerTorsionι_comp_powerActionAdjoint_succ
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealPowerTorsionι I ℱ n ≫
        SheafOfModules.RingedSite.IdealSheaf.powerActionAdjoint.{u, u}
          (idealSheafPowerSubobject I 1) ℱ (n + 1) = 0 := sorry

/-- The canonical inclusion from `I^n`-torsion into `I^(n+1)`-torsion. -/
noncomputable def idealPowerTorsionTransition
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealPowerTorsion I ℱ n ⟶ idealPowerTorsion I ℱ (n + 1) :=
  kernel.lift
      (SheafOfModules.RingedSite.IdealSheaf.powerActionAdjoint.{u, u}
        (idealSheafPowerSubobject I 1) ℱ (n + 1))
      (idealPowerTorsionι I ℱ n)
      (idealPowerTorsionι_comp_powerActionAdjoint_succ I ℱ n) ≫
    (kernelSubobjectIso
      (SheafOfModules.RingedSite.IdealSheaf.powerActionAdjoint.{u, u}
        (idealSheafPowerSubobject I 1) ℱ (n + 1))).inv ≫
    (SheafOfModules.RingedSite.IdealSheaf.powerTorsionSubobjectIso.{u, u}
      (idealSheafPowerSubobject I 1) ℱ (n + 1)).hom

/-- The torsion transition is compatible with the two inclusions into `ℱ`. -/
@[reassoc]
theorem idealPowerTorsionTransition_ι
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealPowerTorsionTransition I ℱ n ≫ idealPowerTorsionι I ℱ (n + 1) =
      idealPowerTorsionι I ℱ n := sorry

/-- The quotient of `ℱ` by its subsheaf of sections annihilated by `I^n`. -/
noncomputable abbrev idealPowerTorsionQuotient
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) : X.Modules :=
  cokernel (idealPowerTorsionι I ℱ n)

/-- The canonical quotient map from `ℱ` to `ℱ / ℱ[I^n]`. -/
noncomputable abbrev idealPowerTorsionQuotientπ
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    ℱ ⟶ idealPowerTorsionQuotient I ℱ n :=
  cokernel.π (idealPowerTorsionι I ℱ n)

/-- The quotient transition `ℱ / ℱ[I^n] ⟶ ℱ / ℱ[I^(n+1)]`. -/
noncomputable def idealPowerTorsionQuotientTransition
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealPowerTorsionQuotient I ℱ n ⟶ idealPowerTorsionQuotient I ℱ (n + 1) :=
  cokernel.desc (idealPowerTorsionι I ℱ n)
    (idealPowerTorsionQuotientπ I ℱ (n + 1)) (by
      rw [← idealPowerTorsionTransition_ι I ℱ n, Category.assoc,
        cokernel.condition]
      simp)

/-- The quotient transition carries the `n`th quotient map to the successor quotient map. -/
@[reassoc]
theorem idealPowerTorsionQuotientTransition_π
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealPowerTorsionQuotientπ I ℱ n ≫
        idealPowerTorsionQuotientTransition I ℱ n =
      idealPowerTorsionQuotientπ I ℱ (n + 1) := sorry

/-- On the complement of the ideal support, quotienting by power torsion does not change
sections. -/
noncomputable instance idealPowerTorsionQuotientπ_app_isIso
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    IsIso ((idealPowerTorsionQuotientπ I ℱ n).val.app (op I.openComplement)) := sorry

/-- The additive group `Hom(I^n, ℱ / ℱ[I^n])`. -/
noncomputable abbrev idealSheafPowerQuotientHomStage
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of
    (idealSheafPowerModule I n ⟶ idealPowerTorsionQuotient I ℱ n)

/-- The transition on quotient Hom stages, obtained by restricting the source and enlarging the
power-torsion quotient. -/
noncomputable def idealSheafPowerQuotientHomTransition
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealSheafPowerQuotientHomStage I ℱ n ⟶
      idealSheafPowerQuotientHomStage I ℱ (n + 1) :=
  AddCommGrpCat.ofHom
    ((Preadditive.rightComp (idealSheafPowerModule I (n + 1))
      (idealPowerTorsionQuotientTransition I ℱ n)).comp
        (Preadditive.leftComp (idealPowerTorsionQuotient I ℱ n)
          (idealSheafPowerTransition I n)))

/-- The sequential diagram `n ↦ Hom(I^n, ℱ / ℱ[I^n])`. -/
noncomputable def idealSheafPowerQuotientHomDiagram
    (I : X.IdealSheafData) (ℱ : X.Modules) : ℕ ⥤ AddCommGrpCat.{u} :=
  Functor.ofSequence (idealSheafPowerQuotientHomTransition I ℱ)

/-- Evaluation of a quotient-valued ideal-power morphism on the support complement. -/
noncomputable def idealSheafPowerQuotientHomToComplementSectionsStageMap
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealSheafPowerQuotientHomStage I ℱ n ⟶ Γ(ℱ, I.openComplement) :=
  AddCommGrpCat.ofHom
    { toFun := fun φ ↦
        inv ((idealPowerTorsionQuotientπ I ℱ n).val.app (op I.openComplement))
          (φ.val.app (op I.openComplement)
            (inv ((idealSheafPowerSubobject I n).arrow.val.app (op I.openComplement))
              (1 : Γ(X, I.openComplement))))
      map_zero' := by
        change (inv ((idealPowerTorsionQuotientπ I ℱ n).val.app
          (op I.openComplement))).hom 0 = 0
        exact map_zero _
      map_add' := by
        intro φ ψ
        change (inv ((idealPowerTorsionQuotientπ I ℱ n).val.app
          (op I.openComplement))).hom
            (φ.val.app (op I.openComplement)
                (inv ((idealSheafPowerSubobject I n).arrow.val.app
                  (op I.openComplement)) (1 : Γ(X, I.openComplement))) +
              ψ.val.app (op I.openComplement)
                (inv ((idealSheafPowerSubobject I n).arrow.val.app
                  (op I.openComplement)) (1 : Γ(X, I.openComplement)))) = _
        exact map_add _ _ _ }

/-- The quotient-valued stage evaluations commute with their transition morphisms. -/
theorem idealSheafPowerQuotientHomToComplementSectionsStageMap_naturality
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    idealSheafPowerQuotientHomTransition I ℱ n ≫
        idealSheafPowerQuotientHomToComplementSectionsStageMap I ℱ (n + 1) =
      idealSheafPowerQuotientHomToComplementSectionsStageMap I ℱ n := sorry

/-- The canonical additive map from `colim_n Hom(I^n, ℱ / ℱ[I^n])` to sections of `ℱ` on the
complement of the ideal support. -/
noncomputable def idealSheafPowerQuotientHomColimitToComplementSections
    (I : X.IdealSheafData) (ℱ : X.Modules) :
    colimit (idealSheafPowerQuotientHomDiagram I ℱ) ⟶ Γ(ℱ, I.openComplement) :=
  Functor.ofSequence.colimitDesc
    (idealSheafPowerQuotientHomTransition I ℱ)
    (idealSheafPowerQuotientHomToComplementSectionsStageMap I ℱ)
    (idealSheafPowerQuotientHomToComplementSectionsStageMap_naturality I ℱ)

/-- The quotient comparison restricts to its defining evaluation on every stage. -/
@[reassoc]
theorem idealSheafPowerQuotientHomColimitToComplementSections_ι
    (I : X.IdealSheafData) (ℱ : X.Modules) (n : ℕ) :
    colimit.ι (idealSheafPowerQuotientHomDiagram I ℱ) n ≫
        idealSheafPowerQuotientHomColimitToComplementSections I ℱ =
      idealSheafPowerQuotientHomToComplementSectionsStageMap I ℱ n := sorry

/-- Restricting the quotient comparison to an affine open agrees with restricting its stage
evaluation. -/
theorem idealSheafPowerQuotientHomColimitToComplementSections_restrict_affine
    (I : X.IdealSheafData) (ℱ : X.Modules) (V : X.affineOpens) (n : ℕ) :
    colimit.ι (idealSheafPowerQuotientHomDiagram I ℱ) n ≫
        idealSheafPowerQuotientHomColimitToComplementSections I ℱ ≫
          ℱ.presheaf.map (homOfLE (inf_le_left :
            I.openComplement ⊓ (V : X.Opens) ≤ I.openComplement)).op =
      idealSheafPowerQuotientHomToComplementSectionsStageMap I ℱ n ≫
        ℱ.presheaf.map (homOfLE (inf_le_left :
          I.openComplement ⊓ (V : X.Opens) ≤ I.openComplement)).op := sorry

/-- For a quasi-compact quasi-separated scheme, a finite-type ideal sheaf, and a
quasi-coherent module sheaf, the canonical quotient ideal-power comparison is an isomorphism. -/
theorem isIso_idealSheafPowerQuotientHomColimitToComplementSections
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (I : X.IdealSheafData) (hI : I.IsFiniteType)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIso (idealSheafPowerQuotientHomColimitToComplementSections I ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
