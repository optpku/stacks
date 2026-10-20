module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleModuleComparison

/-!
# Derived comparison functors on module sheaves

The canonical module comparison and its bounded-below derived adjunction.
-/

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.ObjectProperty Opposite

universe u

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]

#check (AlgebraicGeometry.Scheme.etaleToProEtModuleEssImage X Λ :
  ObjectProperty (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))

#check (AlgebraicGeometry.Scheme.etaleToProEt_modulePlusAdjunction X Λ :
  AlgebraicGeometry.Scheme.etaleToProEt_modulePlusPullback X Λ ⊣
    AlgebraicGeometry.Scheme.etaleToProEt_modulePlusPushforward X Λ)

#check (AlgebraicGeometry.Scheme.etaleToProEt_modulePlusPushforwardRestrict X Λ :
  DerivedCategory.Plus.CohomologyIn
      (AlgebraicGeometry.Scheme.etaleToProEtModuleEssImage X Λ) ⥤
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

#check (AlgebraicGeometry.Scheme.etaleToProEt_modulePlusPullbackLift_compι X Λ :
  AlgebraicGeometry.Scheme.etaleToProEt_modulePlusPullbackLift X Λ ⋙
    (DerivedCategory.Plus.cohomologyIn
      (AlgebraicGeometry.Scheme.etaleToProEtModuleEssImage X Λ)).ι ≅
        AlgebraicGeometry.Scheme.etaleToProEt_modulePlusPullback X Λ)
