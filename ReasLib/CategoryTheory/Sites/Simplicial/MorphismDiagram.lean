/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.ExactMorphismOfSites
public import ReasLib.CategoryTheory.Sites.Simplicial.Total

/-!
# Simplicial diagrams of morphisms of sites

A covariant simplex diagram of sites whose structure maps are morphisms of
sites in the sense of `IsExactMorphismOfSites`: each `u_φ : C.obj m ⥤ C.obj n`
is continuous and `u_φ.sheafPullback` is left exact. The induced morphism of
topoi is `f_φ : Sh(C.obj n) ⟶ Sh(C.obj m)`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SimplicialSites

/-- Structure maps of a covariant simplex diagram compose as functors of stage categories. -/
def map_comp_toFunctor (C : SimplexCategory ⥤ Cat.{v, u}) {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    (C.map ψ).toFunctor ⋙ (C.map φ).toFunctor ≅ (C.map (ψ ≫ φ)).toFunctor :=
  Cat.Hom.toNatIso (eqToIso (C.map_comp ψ φ)).symm

section

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- A covariant simplex diagram of morphisms of sites: each stage is a site and each
structure map `u_φ = (C.map φ).toFunctor : C.obj m ⥤ C.obj n` is an exact morphism of
sites from `(C.obj m, J m)` to `(C.obj n, J n)`. -/
class IsMorphismDiagram : Prop extends IsSiteDiagram C J where
  /-- Each structure map is an exact morphism of sites. -/
  isExactMorphism : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsExactMorphismOfSites (J m).toGrothendieck (J n).toGrothendieck (C.map φ).toFunctor

/-- A morphism diagram is a site diagram whose every structure map is an exact morphism of
sites. -/
theorem IsMorphismDiagram.iff :
    IsMorphismDiagram C J ↔
      IsSiteDiagram C J ∧
        ∀ {m n : SimplexCategory} (φ : m ⟶ n),
          IsExactMorphismOfSites (J m).toGrothendieck (J n).toGrothendieck
            (C.map φ).toFunctor :=
  sorry

variable [h_morphism : IsMorphismDiagram C J]
include h_morphism

/-- Every structure map of a morphism diagram is an exact morphism of sites. -/
instance instIsExactMorphismOfSites {m n : SimplexCategory} (φ : m ⟶ n) :
    IsExactMorphismOfSites (J m).toGrothendieck (J n).toGrothendieck (C.map φ).toFunctor :=
  h_morphism.isExactMorphism φ

/-- The sheaf inverse image along each structure map preserves finite limits. -/
instance instSheafPullbackPreservesFiniteLimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteLimits
      ((C.map φ).toFunctor.sheafPullback (Type w)
        (J m).toGrothendieck (J n).toGrothendieck) :=
  (h_morphism.isExactMorphism φ).preservesFiniteLimits_sheafPullback

/-- The morphism of topoi `f_φ : Sh(C.obj n) ⟶ Sh(C.obj m)` attached to a simplex operator
`φ : m ⟶ n`, presented by the continuous functor `u_φ = (C.map φ).toFunctor`. -/
noncomputable def toposMap {m n : SimplexCategory} (φ : m ⟶ n) :
    MorphismOfTopoiIn (J m).toGrothendieck (J n).toGrothendieck :=
  (C.map φ).toFunctor.morphismOfTopoiInOfContinuous
    (J m).toGrothendieck (J n).toGrothendieck

/-- Inverse images of `f_φ` compose as `Sh(C.obj l) ⥤ Sh(C.obj m) ⥤ Sh(C.obj n)`,
canonically isomorphic to the inverse image of `f_{ψ ≫ φ}` by left-adjoint uniqueness. -/
noncomputable def toposMap_inverseImage_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (toposMap C J ψ).inverseImage ⋙ (toposMap C J φ).inverseImage ≅
      (toposMap C J (ψ ≫ φ)).inverseImage :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        ((C.map ψ).toFunctor.sheafAdjunctionContinuous (Type w)
          (J l).toGrothendieck (J m).toGrothendieck)
        ((C.map φ).toFunctor.sheafAdjunctionContinuous (Type w)
          (J m).toGrothendieck (J n).toGrothendieck)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp' (map_comp_toFunctor C ψ φ) (Type w)
        (J l).toGrothendieck (J m).toGrothendieck (J n).toGrothendieck))
    ((C.map (ψ ≫ φ)).toFunctor.sheafAdjunctionContinuous (Type w)
      (J l).toGrothendieck (J n).toGrothendieck)

/-- Direct images of `f_φ` compose as `Sh(C.obj n) ⥤ Sh(C.obj m) ⥤ Sh(C.obj l)`,
canonically isomorphic to the direct image of `f_{ψ ≫ φ}` by continuous pushforward composition. -/
noncomputable def toposMap_pushforward_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (toposMap C J φ).pushforward ⋙ (toposMap C J ψ).pushforward ≅
      (toposMap C J (ψ ≫ φ)).pushforward :=
  Functor.sheafPushforwardContinuousComp' (map_comp_toFunctor C ψ φ) (Type w)
    (J l).toGrothendieck (J m).toGrothendieck (J n).toGrothendieck

end

/-- A constant diagram of a site is a simplicial diagram of morphisms of sites. -/
instance IsMorphismDiagram.const {C : Type u} [Category.{v} C] (J : Precoverage C) [J.IsSite]
    [HasWeakSheafify J.toGrothendieck (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, (𝟭 C).op.HasLeftKanExtension P] :
    IsMorphismDiagram ((Functor.const SimplexCategory).obj (Cat.of C)) (fun _ ↦ J) :=
  sorry

end CategoryTheory.SimplicialSites
