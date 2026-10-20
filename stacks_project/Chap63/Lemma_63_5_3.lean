/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap63.Lemma_63_5_3_Trace

/-!
# Properties of weighting traces

Lemma 63.5.3: for a locally quasi-finite morphism `f : X ⟶ Y` and a weighting
`w` of `f`, the sheaf traces `Tr_{f, w, F}` are functorial in abelian étale
sheaves `F` and compatible with arbitrary base change, and they induce derived
traces `Tr_{f, w, K} : f_! f⁻¹ K ⟶ K` on `D(Y_étale, Λ)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Lemma 63.5.3 (1): Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes. Let `w : X → ℤ` be a weighting of `f`. The trace maps
`Tr_{f, w, F} : f_! f⁻¹ F ⟶ F` are functorial in the abelian étale sheaf `F`. -/
@[stacks 0GKH]
theorem weightingTrace_natural {w : X → ℤ} (hw : f.IsWeighting w)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (lowerShriek f).map ((etaleAbelianSheafPullback f).map φ) ≫
        weightingTrace f hw G =
      weightingTrace f hw F ≫ φ :=
  sorry

section BaseChange

variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]

/-- Lemma 63.5.3 (2): Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes. Let `w : X → ℤ` be a weighting of `f`. The trace maps
`Tr_{f, w, F}` are compatible with arbitrary base change: for a cartesian
square with `w' = w ∘ g'`, one has
`g⁻¹ Tr_{f, w, F} = Tr_{f', w', g⁻¹ F}` after the identification
`g⁻¹ f_! f⁻¹ F ≅ f'_! (f')⁻¹ g⁻¹ F`. -/
@[stacks 0GKH]
theorem weightingTrace_baseChange {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback g).map (weightingTrace f hw F) =
      (weightingTraceBaseChangeIso f g f' g' h_cart F).hom ≫
        weightingTrace_isPullback f g f' g' h_cart hw
          ((etaleAbelianSheafPullback g).obj F) :=
  sorry

end BaseChange

section Derived

variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f).op]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Lemma 63.5.3 (3): Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes. Let `w : X → ℤ` be a weighting of `f`. Given a ring `Λ` and
`K` in `D(Y_étale, Λ)`, the sheaf traces induce a derived trace
`Tr_{f, w, K} : f_! f⁻¹ K ⟶ K`, functorial in `K` and compatible with
arbitrary base change. -/
@[stacks 0GKH]
def weightingTraceDerived {w : X → ℤ} (hw : f.IsWeighting w)
    (K : EtaleDerived Y Λ) :
    (lowerShriekModuleDerived f Λ).obj
        ((etaleModuleDerivedInverseImage f Λ).obj K) ⟶ K :=
  weightingTraceDerivedHom f Λ hw K

/-- The source-facing derived trace is the objectwise map of
`weightingTraceDerivedNatTrans`. -/
theorem weightingTraceDerived_eq {w : X → ℤ} (hw : f.IsWeighting w)
    (K : EtaleDerived Y Λ) :
    weightingTraceDerived f Λ hw K = weightingTraceDerivedHom f Λ hw K :=
  sorry

end Derived

end AlgebraicGeometry.Scheme.Etale

end
