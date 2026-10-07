module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.ArtinRees
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.GlobalSections

/-!
# Ideal-power Hom colimits and restriction

This file constructs the canonical comparison from the colimit of morphisms out of ideal
powers of a module to morphisms between the restrictions to the complement of the ideal
support.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The additive group of module morphisms from `I^n𝒢` to `ℱ`. -/
noncomputable def idealPowerProductHomStage
    (I : X.IdealSheafData) (𝒢 ℱ : X.Modules) (n : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of ((idealPowerProductSubobject I 𝒢 n : X.Modules) ⟶ ℱ)

/-- Precomposition with `I^(n+1)𝒢 ⟶ I^n𝒢` gives the transition between Hom stages. -/
noncomputable def idealPowerProductHomTransition
    (I : X.IdealSheafData) (𝒢 ℱ : X.Modules) (n : ℕ) :
    idealPowerProductHomStage I 𝒢 ℱ n ⟶
      idealPowerProductHomStage I 𝒢 ℱ (n + 1) :=
  AddCommGrpCat.ofHom
    (Preadditive.leftComp ℱ
      (Subobject.ofLE
        (idealPowerProductSubobject I 𝒢 (n + 1))
        (idealPowerProductSubobject I 𝒢 n)
        (IdealPowerProduct.antitone I 𝒢 n)))

/-- The sequential additive-group diagram `n ↦ Hom(I^n𝒢, ℱ)`. -/
noncomputable def idealPowerProductHomDiagram
    (I : X.IdealSheafData) (𝒢 ℱ : X.Modules) : ℕ ⥤ AddCommGrpCat.{u} :=
  Functor.ofSequence (idealPowerProductHomTransition I 𝒢 ℱ)

/-- On the complement of the ideal support, the inclusion `I^n𝒢 ⟶ 𝒢` becomes an
isomorphism. -/
noncomputable instance idealPowerProductSubobject_restrictArrow_isIso (I : X.IdealSheafData)
    (𝒢 : X.Modules) (n : ℕ) :
    IsIso
      ((restrictFunctor I.openComplement.ι).map
        (idealPowerProductSubobject I 𝒢 n).arrow) := sorry

/-- A morphism `I^n𝒢 ⟶ ℱ` restricts canonically to a morphism `𝒢|_U ⟶ ℱ|_U` on the
complement `U` of the ideal support. -/
noncomputable def idealPowerProductHomToRestrictionStageMap
    (I : X.IdealSheafData) (𝒢 ℱ : X.Modules) (n : ℕ) :
    idealPowerProductHomStage I 𝒢 ℱ n ⟶
      AddCommGrpCat.of
        (((restrictFunctor I.openComplement.ι).obj 𝒢) ⟶
          ((restrictFunctor I.openComplement.ι).obj ℱ)) :=
  AddCommGrpCat.ofHom
    { toFun := fun φ ↦
        inv ((restrictFunctor I.openComplement.ι).map
          (idealPowerProductSubobject I 𝒢 n).arrow) ≫
            (restrictFunctor I.openComplement.ι).map φ
      map_zero' := by simp
      map_add' := by
        intro φ ψ
        rfl }

/-- Restriction to the complement is compatible with the successor transition on ideal-power
Hom stages. -/
theorem idealPowerProductHomToRestrictionStageMap_naturality
    (I : X.IdealSheafData) (𝒢 ℱ : X.Modules) (n : ℕ) :
    idealPowerProductHomTransition I 𝒢 ℱ n ≫
        idealPowerProductHomToRestrictionStageMap I 𝒢 ℱ (n + 1) =
      idealPowerProductHomToRestrictionStageMap I 𝒢 ℱ n := sorry

/-- The canonical additive comparison from `colim_n Hom(I^n𝒢, ℱ)` to
`Hom(𝒢|_U, ℱ|_U)` on the complement `U` of the ideal support. -/
@[stacks 02O8 "ideal-power Hom colimit comparison with restriction"]
noncomputable def idealPowerProductHomColimitToRestriction
    (I : X.IdealSheafData) (𝒢 ℱ : X.Modules) :
    colimit (idealPowerProductHomDiagram I 𝒢 ℱ) ⟶
      AddCommGrpCat.of
        (((restrictFunctor I.openComplement.ι).obj 𝒢) ⟶
          ((restrictFunctor I.openComplement.ι).obj ℱ)) :=
  Functor.ofSequence.colimitDesc
    (idealPowerProductHomTransition I 𝒢 ℱ)
    (idealPowerProductHomToRestrictionStageMap I 𝒢 ℱ)
    (idealPowerProductHomToRestrictionStageMap_naturality I 𝒢 ℱ)

/-- The colimit comparison restricts to its defining restriction map on every Hom stage. -/
@[reassoc]
theorem idealPowerProductHomColimitToRestriction_ι
    (I : X.IdealSheafData) (𝒢 ℱ : X.Modules) (n : ℕ) :
    colimit.ι (idealPowerProductHomDiagram I 𝒢 ℱ) n ≫
        idealPowerProductHomColimitToRestriction I 𝒢 ℱ =
      idealPowerProductHomToRestrictionStageMap I 𝒢 ℱ n := sorry

/-- For a coherent module `𝒢` on a Noetherian scheme and a quasi-coherent module `ℱ`, the
canonical ideal-power Hom comparison to the support complement is an isomorphism. -/
@[stacks 02O8 "ideal-power Hom comparison is an isomorphism"]
noncomputable instance idealPowerProductHomColimitToRestriction_isIso [IsNoetherian X]
    (I : X.IdealSheafData) (𝒢 ℱ : X.Modules)
    [𝒢.IsCoherent] [ℱ.IsQuasicoherent] :
    IsIso (idealPowerProductHomColimitToRestriction I 𝒢 ℱ) := sorry

/-- On a Noetherian scheme, the canonical ideal-power Hom comparison to sections on the
support complement is an isomorphism for every quasi-coherent module. -/
@[stacks 02O8 "ideal-sheaf Hom colimit computes complement sections"]
noncomputable instance idealSheafPowerHomColimitToComplementSections_isIso_of_isNoetherian [IsNoetherian X]
    (I : X.IdealSheafData) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIso (idealSheafPowerHomColimitToComplementSections I ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
