module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Sheafification

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace CategoryTheory.Sheaf

noncomputable section

/-- The sheafification of pointwise extension of scalars along a ring homomorphism. -/
noncomputable def scalarExtensionSheaf
    {X : Scheme.{u}} {Λ Λ' : Type v} [CommRing Λ] [CommRing Λ']
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ')]
    (f : Λ →+* Λ') (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ') :=
  (presheafToSheaf X.smallEtaleTopology (ModuleCat.{v} Λ')).obj
    (F.obj ⋙ ModuleCat.extendScalars f)

namespace IsConstructibleEtaleModule

/-- Scalar extension of a constructible étale sheaf of finite-type modules is constructible. -/
theorem scalarExtension
    {X : Scheme.{u}} {Λ Λ' : Type v} [CommRing Λ] [CommRing Λ']
    [IsNoetherianRing Λ] [IsNoetherianRing Λ']
    [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ')]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ')]
    [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ'),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (f : Λ →+* Λ')
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))
    (hF : IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{v} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
        IsFiniteTypeLocallyConstantModule G) F) :
    IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{v} Λ')
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ')) ↦
        IsFiniteTypeLocallyConstantModule G)
      (scalarExtensionSheaf f F) := sorry

end IsConstructibleEtaleModule

end

end CategoryTheory.Sheaf
