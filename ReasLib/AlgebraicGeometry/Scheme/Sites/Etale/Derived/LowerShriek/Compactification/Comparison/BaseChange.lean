/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.BaseChange

/-!
# Compatibility of the compactification comparison with base change

The two canonical paths compare a fixed compactification model with derived
direct image after a cartesian base change. The imported compactification
base-change interface currently requires a commutative coefficient ring,
although the module-sheaf comparison construction itself works over a ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

variable {X Y X' Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (h_cart : IsPullback g' f' f g)
  [IsSeparated f] [Scheme.Hom.FiniteType f]
  [IsSeparated f'] [Scheme.Hom.FiniteType f']
  [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y']
  (P : Of Y (Over.mk f))
  (Λ : Type u) [CommRing Λ]
  [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X.Etale,
    HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X'.Etale,
    HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y'.Etale,
    HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : P.obj.right.left.Etale,
    HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
    (ModuleCat.{u} Λ)]
  [∀ U : (ambient f g f' g' h_cart P).Etale,
    HasWeakSheafify ((ambient f g f' g' h_cart P).smallEtaleTopology.over U)
      (ModuleCat.{u} Λ)]
  [HasDerivedCategory
    (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback f).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback f').op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback P.obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (ambientToBase f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (interiorLift f g f' g' h_cart P)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
    (etaleExtensionByZero (interiorLift f g f' g' h_cart P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
    (etaleExtensionByZero (interiorLift f g f' g' h_cart P) (ModuleCat.{u} Λ))]

  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
    AddCommGrpCat.{u}]
  [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
    AddCommGrpCat.{u}]
  [HasSheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose X'.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y'.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose P.obj.right.left.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (ambient f g f' g' h_cart P).smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X'.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y'.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [P.obj.right.left.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient f g f' g' h_cart P).smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback
      (ambientToBase f g f' g' h_cart P ≫ g)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback
      (ambientToSource f g f' g' h_cart P ≫
        P.obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : (ambient f g f' g' h_cart P).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback
      (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback
      (interiorLift f g f' g' h_cart P ≫
        ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (g' ≫ Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (smallEtalePullback
      (ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (smallEtalePullback g).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (smallEtalePullback g').op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (smallEtalePullback (ambientToSource f g f' g' h_cart P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (Of.ι P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (interiorLift f g f' g' h_cart P)).op]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]

/-- Whiskered `toPushforward` followed by the star-side mate, from
`g⁻¹ ∘ Rf_!` to `Rf'_* ∘ (g')⁻¹`. -/
irreducible_def toPushforward_baseChangeStar :
    baseChangeDomain f g P Λ ⟶
      (etaleModuleDerivedInverseImage g' Λ ⋙ etaleDerivedPushforward f') := by
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk f).left.Etale, HasWeakSheafify ((Over.mk f).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk f).left.Etale,
      HasWeakSheafify ((Over.mk f).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs
      (HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  exact eqToHom (baseChangeDomain_def f g P Λ) ≫
    whiskerRight (toPushforward (Λ := Λ) (Over.mk f) P)
      (etaleModuleDerivedInverseImage g Λ) ≫
    etaleDerivedPushforwardBaseChange f g f' g' h_cart Λ

/-- Whiskered `toPushforward` from `Rf'_! ∘ (g')⁻¹` to `Rf'_* ∘ (g')⁻¹`. -/
irreducible_def toPushforward_baseChangeCodomain :
    baseChangeCodomain f g f' g' h_cart P Λ ⟶
      (etaleModuleDerivedInverseImage g' Λ ⋙ etaleDerivedPushforward f') := by
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `∀ U : X'.Etale, HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk f').left.Etale, HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk f').left.Etale,
      HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs
      (HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  exact eqToHom (baseChangeCodomain_def f g f' g' h_cart P Λ) ≫
    whiskerLeft (etaleModuleDerivedInverseImage g' Λ)
      (toPushforward (Λ := Λ) (Over.mk f')
        (compactificationPullback f g f' g' h_cart P))

/-- Composite of shriek-side base change with whiskered `toPushforward`. -/
irreducible_def toPushforward_baseChange_comp :
    baseChangeDomain f g P Λ ⟶
      (etaleModuleDerivedInverseImage g' Λ ⋙ etaleDerivedPushforward f') :=
  baseChange f g f' g' h_cart P Λ ≫
    toPushforward_baseChangeCodomain f g f' g' h_cart P Λ

/-- Compatibility of `toPushforward` with `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` and
the canonical derived pushforward mate. -/
theorem toPushforward_baseChange_compat :
    toPushforward_baseChangeStar f g f' g' h_cart P Λ =
      toPushforward_baseChange_comp f g f' g' h_cart P Λ :=
  sorry

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

end
