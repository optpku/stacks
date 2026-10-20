module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedTopos
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat

@[expose] public section
open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory
noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable (f : X ⟶ Y) (τ : StandardTopology) [HasSmallAssociatedTypeSections f τ]

/-- Restriction of scalars along the inverse-image structure map of
`associatedRingedToposHom f τ` is a right adjoint. -/
theorem associatedRingedToposHom_restrictScalars_isRightAdjoint :
    (SheafOfModules.restrictScalars.{u}
      (associatedRingedToposHom f τ).structureMap).IsRightAdjoint :=
  sorry

/-- The morphism of associated `τ`-ringed topoi induced by a 1-morphism of
categories fibred in groupoids is flat. -/
theorem associatedRingedToposHom_isFlat :
    @RingedSite.ToposHom.IsFlat.{u + 1, u, u + 1, u, u}
      _ _ inferInstance inferInstance (associatedRingedToposHom f τ)
      (associatedRingedToposHom_restrictScalars_isRightAdjoint f τ) := sorry

/-- Flatness of `associatedRingedToposHom f τ` together with invertibility of its
inverse-image structure map, recording the identification `f⁻¹ 𝒪_Y ≅ 𝒪_X`. -/
theorem associatedRingedToposHom_isFlat_spec :
    @RingedSite.ToposHom.IsFlat.{u + 1, u, u + 1, u, u}
        _ _ inferInstance inferInstance (associatedRingedToposHom f τ)
        (associatedRingedToposHom_restrictScalars_isRightAdjoint f τ) ∧
      IsIso (associatedRingedToposHom f τ).structureMap := sorry

end AlgebraicGeometry.GroupoidsOver

