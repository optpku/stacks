module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pullback.Module
public import stacks_project.Chap85.Lemma_85_11_1_Flat
public import stacks_project.Chap96.Lemma_96_6_2_RingedTopos

/-!
# Flatness of associated morphisms of ringed topoi and big sites

A 1-morphism of categories fibred in groupoids induces a flat morphism of associated
`τ`-ringed topoi, because the inverse-image structure map is the identification
`f⁻¹ 𝒪_Y ≅ 𝒪_X`. The same site-level flatness holds for the morphism of big `τ`-sites
induced by an arbitrary scheme morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- Restriction of scalars along the inverse-image structure map of
`associatedRingedToposHom f τ` is a right adjoint. -/
instance associatedRingedToposHom_restrictScalars_isRightAdjoint (f : X ⟶ Y)
    (τ : StandardTopology) :
    (SheafOfModules.restrictScalars.{u}
      (associatedRingedToposHom f τ).structureMap).IsRightAdjoint :=
  sorry

/-- The morphism of associated `τ`-ringed topoi induced by a 1-morphism of
categories fibred in groupoids is flat. -/
instance associatedRingedToposHom_isFlat (f : X ⟶ Y) (τ : StandardTopology) :
    RingedSite.ToposHom.IsFlat.{u + 1, u, u + 1, u, u}
      (associatedRingedToposHom f τ) :=
  sorry

/-- Flatness of `associatedRingedToposHom f τ` together with invertibility of its
inverse-image structure map, recording the identification `f⁻¹ 𝒪_Y ≅ 𝒪_X`. -/
theorem associatedRingedToposHom_isFlat_spec (f : X ⟶ Y) (τ : StandardTopology) :
    RingedSite.ToposHom.IsFlat.{u + 1, u, u + 1, u, u}
        (associatedRingedToposHom f τ) ∧
      IsIso (associatedRingedToposHom f τ).structureMap :=
  sorry

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.StandardTopology.Big

/-- Module pushforward along the morphism of big `τ`-sites induced by a scheme
morphism has a left adjoint. -/
instance pullbackRingedHom_modulePushforwardIsRightAdjoint (τ : StandardTopology)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((pullbackRingedHom τ f).modulePushforward.{u}).IsRightAdjoint :=
  pullbackRingedHom_modulePushforward_isRightAdjoint τ f

/-- The morphism of big `τ`-sites induced by a scheme morphism is flat. -/
instance pullbackRingedHom_isFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (τ : StandardTopology) :
    RingedSite.Hom.IsFlat.{u} (pullbackRingedHom τ f) :=
  sorry

end AlgebraicGeometry.StandardTopology.Big
