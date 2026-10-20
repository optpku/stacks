module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleModuleComparison
import StacksCheckRecall

/-!
# Lemma 61.19.8

Canonical inverse image on module sheaves has weak Serre essential image and
induces an equivalence of bounded-below derived categories, with quasi-inverse
given by restricted right-derived direct image.
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

/- Lemma 61.19.8. Inverse image induces an equivalence onto the bounded-below
complexes whose cohomology lies in its weak Serre essential image. The
quasi-inverse is the restriction of the canonical right-derived direct image. -/
@[stacks 09B1] #check
  (AlgebraicGeometry.Scheme.etaleToProEt_modulePlusPullbackLift_isEquivalence X Λ :
    Functor.IsEquivalence
      (AlgebraicGeometry.Scheme.etaleToProEt_modulePlusPullbackLift X Λ))

#check (AlgebraicGeometry.Scheme.etaleToProEtModuleEssImage_isWeakSerre X Λ :
  IsWeakSerreClass (AlgebraicGeometry.Scheme.etaleToProEtModuleEssImage X Λ))

#check (AlgebraicGeometry.Scheme.etaleToProEt_sheafAdjunction_module_unit_app_isIso X Λ :
  ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
    IsIso ((AlgebraicGeometry.Scheme.etaleToProEt_sheafAdjunction X
      (ModuleCat.{u + 1} Λ)).unit.app F))

#check (AlgebraicGeometry.Scheme.etaleToProEt_modulePlusAdjunction_unit_app_isIso X Λ :
  ∀ K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    IsIso ((AlgebraicGeometry.Scheme.etaleToProEt_modulePlusAdjunction X Λ).unit.app K))

#check (AlgebraicGeometry.Scheme.etaleToProEt_modulePlusAdjunction_counit_app_isIso X Λ :
  ∀ K : DerivedCategory.Plus.CohomologyIn
      (AlgebraicGeometry.Scheme.etaleToProEtModuleEssImage X Λ),
    IsIso
      ((AlgebraicGeometry.Scheme.etaleToProEt_modulePlusAdjunction X Λ).counit.app
        ((DerivedCategory.Plus.cohomologyIn
          (AlgebraicGeometry.Scheme.etaleToProEtModuleEssImage X Λ)).ι.obj K)))

#check (AlgebraicGeometry.Scheme.etaleToProEt_modulePlusPushforwardRestrict X Λ :
  DerivedCategory.Plus.CohomologyIn
      (AlgebraicGeometry.Scheme.etaleToProEtModuleEssImage X Λ) ⥤
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
