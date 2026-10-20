module

import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.Affine
import StacksCheckRecall
import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

open CategoryTheory
open scoped AlgebraicGeometry

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.35.3 (1): a quasi-coherent derived object is perfect over a flat,
locally finitely presented morphism exactly when its derived sections on every compatible pair
of affine opens are perfect over the target section ring. -/
@[stacks 0DI2] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isPerfectRelativeTo_iff_affineSectionsPerfect :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
        CategoryTheory.DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
      (E : DerivedQCoh X),
      AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo f E.obj ↔
        ∀ (V : S.affineOpens) (U : X.affineOpens)
          (e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)),
          DerivedCategory.IsPerfect
            ((Modules.Kunneth.globalSectionsOver
              (f.resLE (V : S.Opens) (U : X.Opens) e)).obj
                ((DerivedQCoh.OpenImmersion.pullback (U : X.Opens).ι).obj E).obj))

/- Lemma 36.35.3 (2): relative perfectness is equivalent to perfectness of derived sections
on the members of affine covers of the inverse images of one affine cover of the base. -/
@[stacks 0DI2] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isPerfectRelativeTo_iff_affineCoverSectionsPerfect :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
        CategoryTheory.DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
      (E : DerivedQCoh X),
      AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo f E.obj ↔
        ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover, ∀ i : 𝒰.I₀,
            DerivedCategory.IsPerfect
              ((Modules.Kunneth.globalSectionsOver
                (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j)).obj
                  ((DerivedQCoh.OpenImmersion.pullback
                    (𝒰.f i ≫ (𝒱.openCover.pullback₁ f).f j)).obj E).obj))

end AlgebraicGeometry.Scheme.DerivedQCoh
