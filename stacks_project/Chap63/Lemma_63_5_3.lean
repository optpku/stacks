/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap59.Definition_59_77_1
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.Weighting.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.Weighting.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.Weighting.Composition

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

/- Lemma 63.5.3 (1): weighting traces are functorial in the abelian étale sheaf. -/
@[stacks 0GKH] #check (AlgebraicGeometry.Scheme.Etale.weightingTrace_natural f :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G),
    (lowerShriek f).map ((etaleAbelianSheafPullback f).map φ) ≫
        weightingTrace f hw G =
      weightingTrace f hw F ≫ φ)

section BaseChange

variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]

/- Lemma 63.5.3 (2): weighting traces commute with arbitrary base change. -/
@[stacks 0GKH] #check (AlgebraicGeometry.Scheme.Etale.weightingTrace_baseChange f g f' g' h_cart :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}),
    (etaleAbelianSheafPullback g).map (weightingTrace f hw F) =
      (weightingTraceBaseChangeIso f g f' g' h_cart F).hom ≫
        weightingTrace_isPullback f g f' g' h_cart hw
          ((etaleAbelianSheafPullback g).obj F))

end BaseChange

section Derived

variable (Λ : Type u) [Ring Λ]
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

/- Lemma 63.5.3 (3): the induced derived trace exists over any ring. -/
@[stacks 0GKH] #check (AlgebraicGeometry.Scheme.Etale.weightingTraceDerived f Λ :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))),
    (lowerShriekModuleDerived f Λ).obj
        ((etaleModuleDerivedInverseImage f Λ).obj K) ⟶ K)

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceDerived_natural f Λ :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    {K L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))} (φ : K ⟶ L),
    (lowerShriekModuleDerived f Λ).map
          ((etaleModuleDerivedInverseImage f Λ).map φ) ≫
        weightingTraceDerived f Λ hw L =
      weightingTraceDerived f Λ hw K ≫ φ)

variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g').op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f').op]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceDerived_baseChange f Λ g f' g' h_cart :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))),
    (etaleModuleDerivedInverseImage g Λ).map
        (weightingTraceDerived f Λ hw K) =
      (weightingTraceDerivedBaseChangeIso f Λ g f' g' h_cart K).hom ≫
        weightingTraceDerived_isPullback f Λ g f' g' h_cart hw
          ((etaleModuleDerivedInverseImage g Λ).obj K))

end Derived

end AlgebraicGeometry.Scheme.Etale

end
