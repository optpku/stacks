module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Characterization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.TorDimension.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

/-!
# Affine criteria for relative perfectness

This file characterizes relative perfectness of a derived module with quasicoherent
cohomology in terms of perfect derived sections over affine opens.
-/

open CategoryTheory
open scoped AlgebraicGeometry

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- A derived module with quasicoherent cohomology is perfect relative to a flat, locally
finitely presented morphism exactly when its derived sections over every compatible pair of
affine opens are perfect over the target section ring. -/
theorem isPerfectRelativeTo_iff_affineSectionsPerfect {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) :
    IsPerfectRelativeTo f E.obj ↔
      ∀ (V : S.affineOpens) (U : X.affineOpens)
        (e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)),
        DerivedCategory.IsPerfect
          ((Modules.Kunneth.globalSectionsOver
            (f.resLE (V : S.Opens) (U : X.Opens) e)).obj
              ((DerivedQCoh.OpenImmersion.pullback (U : X.Opens).ι).obj E).obj) := sorry

/-- A derived module with quasicoherent cohomology is perfect relative to a flat, locally
finitely presented morphism exactly when its derived sections are perfect on affine covers of
the inverse images of the members of an affine cover of the base. -/
theorem isPerfectRelativeTo_iff_affineCoverSectionsPerfect {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) :
    IsPerfectRelativeTo f E.obj ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover, ∀ i : 𝒰.I₀,
          DerivedCategory.IsPerfect
            ((Modules.Kunneth.globalSectionsOver
              (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j)).obj
                ((DerivedQCoh.OpenImmersion.pullback
                  (𝒰.f i ≫ (𝒱.openCover.pullback₁ f).f j)).obj E).obj) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
