/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Comparison.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Comparison.BaseChange
import StacksCheckRecall

/-!
# Derived étale comparison from lower shriek to direct image

A separated finite-type morphism with quasi-compact quasi-separated target
has a functorial comparison from its compactification lower-shriek model to
derived direct image. Independence holds on bounded-below torsion complexes,
or on all complexes for a torsion coefficient ring. The comparison respects
the canonical composition and base-change maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

universe u

section Comparison

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (P : Of Y X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [h_interiorLeftKanExtension : ∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [h_extensionByZero_additive :
  (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
variable [h_extensionByZero_limits : PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [h_extensionByZero_colimits : PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]

/- Remark 63.9.5 (1): Let `f : X ⟶ Y` be a finite type separated morphism of
schemes with `Y` quasi-compact and quasi-separated. There is a functorial
comparison `Rf_! K ⟶ Rf_* K` on objects of `D⁺_tors(X_étale, Λ)`, or of
`D(X_étale, Λ)` if `Λ` is torsion, constructed from a compactification
`j : X ⟶ X̄` over `Y` by promoting `j_! ⟶ j_*` of Lemma 59.70.6. -/
@[stacks 0H6X] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.toPushforward X P :
  etaleDerivedLowerShriek X P ⟶
    (etaleDerivedPushforward X.hom :
      DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))))

variable {Q : Of Y X} (φ : P ⟶ Q)
variable [HasSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Q.obj.right.left.Etale,
  HasWeakSheafify (Q.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]

variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]

variable [HasSheafCompose X.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose P.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose Q.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Q.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι P)).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι Q)).op]

/- Remark 63.9.5 (4): the resulting transformation is independent of the
choice of compactification on objects of `D⁺_tors(X_étale, Λ)`. -/
@[stacks 0H6X] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.toPushforward_isoOfHom_of_isGE_isTorsion X P φ :
  ∀ (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))),
    etaleDerivedIsTorsion K → ∀ (n : ℤ), ∀ [DerivedCategory.IsGE K n],
      (isoOfHom X Λ φ).app K ≫ (toPushforward X P).app K =
        (toPushforward X Q).app K)

/- Remark 63.9.5 (5): if `Λ` is torsion, the resulting transformation is
independent of the compactification as a natural transformation on
`D(X_étale, Λ)`. -/
@[stacks 0H6X] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.toPushforward_isoOfHom_of_isTorsion X P φ :
  AddMonoid.IsTorsion Λ →
    isoOfHom X Λ φ ≫ toPushforward X P = toPushforward X Q)

end Comparison

section Composition

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  (C : CompDiagram X g)
  (Λ : Type u) [CommRing Λ]
  [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X.left.Etale,
    HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Z.Etale,
    HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (CompDiagram.interior X g C).Etale,
    HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U)
      (ModuleCat.{u} Λ)]
  [HasDerivedCategory
    (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : C.P_bar.obj.right.left.Etale,
    HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U)
      (ModuleCat.{u} Λ)]
  [HasDerivedCategory
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : C.P_g.obj.right.left.Etale,
    HasWeakSheafify (C.P_g.obj.right.left.smallEtaleTopology.over U)
      (ModuleCat.{u} Λ)]
  [HasDerivedCategory
    (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [IsOpenImmersion (Of.ι C.P_g)]
  [Etale (Of.ι C.P_g)]
  [IsSeparated (Of.ι C.P_g)]
  [LocallyQuasiFinite (Of.ι C.P_g)]
  [LocallyOfFiniteType (Of.ι C.P_g)]
  [IsSeparated (CompDiagram.openImmersion X g C)]
  [LocallyQuasiFinite (CompDiagram.openImmersion X g C)]
  [LocallyOfFiniteType (CompDiagram.openImmersion X g C)]
  [IsSeparated (Of.ι (CompDiagram.ofInterior X g C))]
  [LocallyQuasiFinite (Of.ι (CompDiagram.ofInterior X g C))]
  [LocallyOfFiniteType (Of.ι (CompDiagram.ofInterior X g C))]
  [IsSeparated (Of.ι (CompDiagram.ofComposite X g C))]
  [LocallyQuasiFinite
    (Of.ι (CompDiagram.ofComposite X g C))]
  [LocallyOfFiniteType
    (Of.ι (CompDiagram.ofComposite X g C))]
  [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (CompDiagram.interior X g C).smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify C.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafCompose X.left.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (CompDiagram.interior X g C).smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose C.P_bar.obj.right.left.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose C.P_g.obj.right.left.smallEtaleTopology
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(CompDiagram.interior X g C).smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [C.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [C.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior X g C).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction
      (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior X g C).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction
      (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (CompDiagram.openImmersion X g C)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction
      (Of.ι (CompDiagram.ofComposite X g C))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (Of.ι C.P_g)).op]
  [(etaleExtensionByZero (Of.ι (CompDiagram.ofInterior X g C))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
    (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
    (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (Of.ι C.P_g) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
    (etaleExtensionByZero (Of.ι C.P_g) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
    (etaleExtensionByZero (Of.ι C.P_g) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (CompDiagram.openImmersion X g C)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
    (etaleExtensionByZero (CompDiagram.openImmersion X g C) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
    (etaleExtensionByZero (CompDiagram.openImmersion X g C) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite X g C))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite X g C))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite X g C))
    (ModuleCat.{u} Λ))]

/- Remark 63.9.5 (2): this transformation is compatible with the isomorphism
`Rg_! ∘ Rf_! ⟶ R(g ∘ f)_!` of Lemma 63.9.2 and the isomorphism
`Rg_* ∘ Rf_* ⟶ R(g ∘ f)_*` of Cohomology on Sites, Lemma 21.19.2. -/
@[stacks 0H6X] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.toPushforward_comp_compat X g C Λ :
  toPushforward_compDomain X g C Λ ≫
    (asIso (etaleDerivedPushforwardComp X.hom g Λ)).inv =
      comp X g C Λ ≫ toPushforward_compCodomain X g C Λ)

end Composition

section BaseChange

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

/- Remark 63.9.5 (3): this transformation is compatible with the isomorphism
`g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of Lemma 63.9.4 and the base change map of
Cohomology on Sites, Remark 21.19.3. -/
@[stacks 0H6X] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.toPushforward_baseChange_compat f g f' g' h_cart P Λ :
  toPushforward_baseChangeStar f g f' g' h_cart P Λ =
    toPushforward_baseChange_comp f g f' g' h_cart P Λ)

end BaseChange

end
