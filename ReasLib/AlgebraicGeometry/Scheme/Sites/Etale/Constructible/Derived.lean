/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable (f : X ⟶ Y)

section InverseImage

variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [hAdd : @CategoryTheory.Functor.Additive
    (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))
    (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) _ _
    Abelian.toPreadditive Abelian.toPreadditive
    (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ))]
variable [PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ))]

/-- The derived inverse image on étale sheaves of modules is the functor on derived
categories induced by the exact small étale inverse-image functor. -/
noncomputable def smallEtaleInverseImageDerived :
    DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :=
  (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ)).mapDerivedCategory

end InverseImage

section Constructibility

variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Z : Scheme.{u}) (U : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [hAdd : @CategoryTheory.Functor.Additive
    (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))
    (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) _ _
    Abelian.toPreadditive Abelian.toPreadditive
    (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ))]
variable [PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ))]

/-- Over a Noetherian coefficient ring, derived inverse image along a scheme morphism
preserves constructibility of all cohomology sheaves. -/
theorem smallEtaleInverseImageDerived_mem_constructibleCategory
    (K : DerivedCategory.CohomologyIn
      (Sheaf.IsConstructibleEtaleModule (X := Y)
        (fun {Z} g ↦ (Sheaf.smallEtaleInverseImage g (ModuleCat.{v} Λ)).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))) :
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule (X := X)
        (fun {Z} g ↦ (Sheaf.smallEtaleInverseImage g (ModuleCat.{v} Λ)).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((smallEtaleInverseImageDerived f).obj K.obj) := sorry

/-- Every homology sheaf of the derived inverse image of a complex with constructible
étale module cohomology is constructible. -/
theorem smallEtaleInverseImageDerived_homology_isConstructibleEtaleModule
    (K : DerivedCategory.CohomologyIn
      (Sheaf.IsConstructibleEtaleModule (X := Y)
        (fun {Z} g ↦ (Sheaf.smallEtaleInverseImage g (ModuleCat.{v} Λ)).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)))
    (n : ℤ) :
    Sheaf.IsConstructibleEtaleModule (X := X)
      (fun {Z} g ↦ (Sheaf.smallEtaleInverseImage g (ModuleCat.{v} Λ)).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) n).obj
        ((smallEtaleInverseImageDerived f).obj K.obj)) := sorry

end Constructibility

end AlgebraicGeometry.Scheme
