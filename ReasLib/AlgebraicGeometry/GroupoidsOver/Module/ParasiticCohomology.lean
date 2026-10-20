module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Modules
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Parasitic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.TopologyComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Cohomology

/-! # Cohomology and higher direct images of parasitic modules -/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The higher direct image of an associated-site module is the value of the
right derived functor of the associated ringed-topos module direct image. -/
abbrev associatedModules.higherDirectImage {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (τ : StandardTopology)
    [hsize : HasSmallAssociatedTypeSections f τ]
    [aX : Abelian (RingedSite.ModuleCat.{u} (associatedRingedSite X τ))]
    [aY : Abelian (RingedSite.ModuleCat.{u} (associatedRingedSite Y τ))]
    (F : RingedSite.ModuleCat.{u} (associatedRingedSite X τ)) (i : ℕ)
    [hI : HasInjectiveResolutions (RingedSite.ModuleCat.{u} (associatedRingedSite X τ))] :
    RingedSite.ModuleCat.{u} (associatedRingedSite Y τ) :=
  (@Functor.rightDerived _ _ _ _ aX
      (by convert hI using 1; exact Subsingleton.elim _ _) aY
    ((associatedRingedToposHom f τ).modulePushforward)
    (by
      convert associatedRingedToposHom_modulePushforward_additive f τ using 1 <;>
        first
        | exact @Subsingleton.elim _
            (@subsingleton_preadditive_of_hasBinaryBiproducts _ _
              (@Preadditive.preadditiveHasZeroMorphisms _ _ aX.toPreadditive)
              (@Abelian.hasBinaryBiproducts _ _ aX)) _ _
        | exact @Subsingleton.elim _
            (@subsingleton_preadditive_of_hasBinaryBiproducts _ _
              (@Preadditive.preadditiveHasZeroMorphisms _ _ aY.toPreadditive)
              (@Abelian.hasBinaryBiproducts _ _ aY)) _ _) i).obj F

/-- Higher direct image is computed by the right derived module direct image functor. -/
theorem associatedModules.higherDirectImage_eq {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (τ : StandardTopology)
    [hsize : HasSmallAssociatedTypeSections f τ]
    [aX : Abelian (RingedSite.ModuleCat.{u} (associatedRingedSite X τ))]
    [aY : Abelian (RingedSite.ModuleCat.{u} (associatedRingedSite Y τ))]
    (F : RingedSite.ModuleCat.{u} (associatedRingedSite X τ)) (i : ℕ)
    [hI : HasInjectiveResolutions (RingedSite.ModuleCat.{u} (associatedRingedSite X τ))] :
    associatedModules.higherDirectImage f τ F i =
      (@Functor.rightDerived _ _ _ _ aX
          (by convert hI using 1; exact Subsingleton.elim _ _) aY
        ((associatedRingedToposHom f τ).modulePushforward)
        (by
          convert associatedRingedToposHom_modulePushforward_additive f τ using 1 <;>
            first
            | exact @Subsingleton.elim _
                (@subsingleton_preadditive_of_hasBinaryBiproducts _ _
                  (@Preadditive.preadditiveHasZeroMorphisms _ _ aX.toPreadditive)
                  (@Abelian.hasBinaryBiproducts _ _ aX)) _ _
            | exact @Subsingleton.elim _
                (@subsingleton_preadditive_of_hasBinaryBiproducts _ _
                  (@Preadditive.preadditiveHasZeroMorphisms _ _ aY.toPreadditive)
                  (@Abelian.hasBinaryBiproducts _ _ aY)) _ _) i).obj F :=
  rfl

/-- A parasitic module on an algebraic stack has zero cohomology in every degree
for the étale or fppf topology. -/
theorem isZero_cohomology_of_isParasitic {X : GroupoidsOver S} [AlgebraicStack X]
    {τ : StandardTopology} (hτ : τ = .etale ∨ τ = .fppf)
    [aX : Abelian (RingedSite.ModuleCat.{u} (associatedRingedSite X τ))]
    (F : RingedSite.ModuleCat.{u} (associatedRingedSite X τ))
    [IsParasitic ((PresheafOfModules.restrictScalars
      (associatedStructurePresheafIso X τ).hom).obj F.val)]
    (i : ℕ) [HasExt (RingedSite.ModuleCat.{u} (associatedRingedSite X τ))] :
    IsZero (RingedSite.Hom.moduleGlobalCohomology (X := associatedRingedSite X τ) F i) :=
  sorry

/-- Higher direct images of parasitic modules along morphisms of algebraic stacks
are parasitic in the étale or fppf topology. -/
theorem associatedModules.isParasitic_higherDirectImage
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {τ : StandardTopology} (hτ : τ = .etale ∨ τ = .fppf) (f : X ⟶ Y)
    [hsize : HasSmallAssociatedTypeSections f τ]
    [aX : Abelian (RingedSite.ModuleCat.{u} (associatedRingedSite X τ))]
    [aY : Abelian (RingedSite.ModuleCat.{u} (associatedRingedSite Y τ))]
    (F : RingedSite.ModuleCat.{u} (associatedRingedSite X τ))
    [IsParasitic ((PresheafOfModules.restrictScalars
      (associatedStructurePresheafIso X τ).hom).obj F.val)] (i : ℕ)
    [HasInjectiveResolutions (RingedSite.ModuleCat.{u} (associatedRingedSite X τ))] :
    IsParasitic ((PresheafOfModules.restrictScalars
      (associatedStructurePresheafIso Y τ).hom).obj
        (associatedModules.higherDirectImage f τ F i).val) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
