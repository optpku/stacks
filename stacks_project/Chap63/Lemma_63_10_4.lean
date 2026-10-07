module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_7_3_MayerVietoris
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative Mayer–Vietoris triangle for derived étale lower shriek
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Functor
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) (P : Compactification.Of Y X)
variable (U V : X.left.Opens) (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [CompactSpace U] [CompactSpace V]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [HasWeakSheafify U.toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : U.toScheme.Etale,
  HasWeakSheafify (U.toScheme.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [Abelian (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasWeakSheafify V.toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : V.toScheme.Etale,
  HasWeakSheafify (V.toScheme.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [Abelian (Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasWeakSheafify (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ W : (U ⊓ V).toScheme.Etale,
  HasWeakSheafify ((U ⊓ V).toScheme.smallEtaleTopology.over W) (ModuleCat.{u} Λ)]
variable [Abelian (Sheaf (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory
  (Sheaf (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : U.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (U.ι)).op.HasLeftKanExtension F]
variable [∀ F : V.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (V.ι)).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction ((U ⊓ V).ι)).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction ((X.left.homOfLE (inf_le_left : U ⊓ V ≤ U)))).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction ((X.left.homOfLE (inf_le_right : U ⊓ V ≤ V)))).op.HasLeftKanExtension F]
variable [(etaleRestrictionSheaf (U.ι) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf (U.ι) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf (U.ι) (ModuleCat.{u} Λ))]
variable [(etaleRestrictionSheaf (V.ι) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf (V.ι) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf (V.ι) (ModuleCat.{u} Λ))]
variable [(etaleRestrictionSheaf ((U ⊓ V).ι) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf ((U ⊓ V).ι) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf ((U ⊓ V).ι) (ModuleCat.{u} Λ))]
variable [(etaleRestrictionSheaf ((X.left.homOfLE (inf_le_left : U ⊓ V ≤ U)))
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf ((X.left.homOfLE (inf_le_left : U ⊓ V ≤ U)))
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf ((X.left.homOfLE (inf_le_left : U ⊓ V ≤ U)))
    (ModuleCat.{u} Λ))]
variable [(etaleRestrictionSheaf ((X.left.homOfLE (inf_le_right : U ⊓ V ≤ V)))
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf ((X.left.homOfLE (inf_le_right : U ⊓ V ≤ V)))
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf ((X.left.homOfLE (inf_le_right : U ⊓ V ≤ V)))
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (U.ι) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (U.ι) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (U.ι) (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (V.ι) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (V.ι) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (V.ι) (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero ((U ⊓ V).ι) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero ((U ⊓ V).ι) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero ((U ⊓ V).ι) (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (X.left.homOfLE (inf_le_left : U ⊓ V ≤ U))
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (X.left.homOfLE (inf_le_left : U ⊓ V ≤ U))
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (X.left.homOfLE (inf_le_left : U ⊓ V ≤ U))
    (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (X.left.homOfLE (inf_le_right : U ⊓ V ≤ V))
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (X.left.homOfLE (inf_le_right : U ⊓ V ≤ V))
    (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (X.left.homOfLE (inf_le_right : U ⊓ V ≤ V))
    (ModuleCat.{u} Λ))]
variable [(etaleRestrictionSheaf (U.ι) (ModuleCat.{u} Λ) ⋙
    etaleRestrictionSheaf ((X.left.homOfLE (inf_le_left : U ⊓ V ≤ U)))
      (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (U.ι) (ModuleCat.{u} Λ) ⋙
    etaleRestrictionSheaf ((X.left.homOfLE (inf_le_left : U ⊓ V ≤ U)))
      (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (U.ι) (ModuleCat.{u} Λ) ⋙
    etaleRestrictionSheaf ((X.left.homOfLE (inf_le_left : U ⊓ V ≤ U)))
      (ModuleCat.{u} Λ))]
variable [(etaleRestrictionSheaf (V.ι) (ModuleCat.{u} Λ) ⋙
    etaleRestrictionSheaf ((X.left.homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (V.ι) (ModuleCat.{u} Λ) ⋙
    etaleRestrictionSheaf ((X.left.homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (V.ι) (ModuleCat.{u} Λ) ⋙
    etaleRestrictionSheaf ((X.left.homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (X.left.homOfLE (inf_le_left : U ⊓ V ≤ U))
    (ModuleCat.{u} Λ) ⋙ etaleExtensionByZero (U.ι) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (X.left.homOfLE (inf_le_left : U ⊓ V ≤ U))
    (ModuleCat.{u} Λ) ⋙ etaleExtensionByZero (U.ι) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (X.left.homOfLE (inf_le_left : U ⊓ V ≤ U))
    (ModuleCat.{u} Λ) ⋙ etaleExtensionByZero (U.ι) (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (X.left.homOfLE (inf_le_right : U ⊓ V ≤ V))
    (ModuleCat.{u} Λ) ⋙ etaleExtensionByZero (V.ι) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (X.left.homOfLE (inf_le_right : U ⊓ V ≤ V))
    (ModuleCat.{u} Λ) ⋙ etaleExtensionByZero (V.ι) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (X.left.homOfLE (inf_le_right : U ⊓ V ≤ V))
    (ModuleCat.{u} Λ) ⋙ etaleExtensionByZero (V.ι) (ModuleCat.{u} Λ))]

namespace etaleDerivedLowerShriek

/-- The first relative Mayer–Vietoris map
`Rf_! (j_{U ∩ V!}((-) |_{U ∩ V})) ⟶ Rf_! (j_{U!}((-) |_U)) ⊞ Rf_! (j_{V!}((-) |_V))`,
obtained by whiskering the maps to each open with `etaleDerivedLowerShriek X P`
and lifting to the biproduct of images. -/
noncomputable def mayerVietorisToBiprod :
    etaleDerivedExtensionByZeroRestrict ((U ⊓ V).ι) Λ ⋙
        etaleDerivedLowerShriek X P ⟶
      (etaleDerivedExtensionByZeroRestrict (U.ι) Λ ⋙
          etaleDerivedLowerShriek X P) ⊞
        (etaleDerivedExtensionByZeroRestrict (V.ι) Λ ⋙
          etaleDerivedLowerShriek X P) :=
  biprod.lift
    (whiskerRight (mayerVietorisLowerShriekToLeft U V Λ)
      (etaleDerivedLowerShriek X P))
    (whiskerRight (mayerVietorisLowerShriekToRight U V Λ)
      (etaleDerivedLowerShriek X P))

/-- The second relative Mayer–Vietoris map
`Rf_! (j_{U!}((-) |_U)) ⊞ Rf_! (j_{V!}((-) |_V)) ⟶ Rf_!`, with a minus on the
`V`-component, obtained by descending the whiskered open-immersion counits. -/
noncomputable def mayerVietorisFromBiprod :
    (etaleDerivedExtensionByZeroRestrict (U.ι) Λ ⋙
        etaleDerivedLowerShriek X P) ⊞
      (etaleDerivedExtensionByZeroRestrict (V.ι) Λ ⋙
        etaleDerivedLowerShriek X P) ⟶
      etaleDerivedLowerShriek X P :=
  biprod.desc
    (whiskerRight (etaleDerivedExtensionByZeroAdjunction (U.ι) Λ).counit
        (etaleDerivedLowerShriek X P) ≫
      (Functor.leftUnitor (etaleDerivedLowerShriek X P)).hom)
    (whiskerRight (-(etaleDerivedExtensionByZeroAdjunction (V.ι) Λ).counit)
        (etaleDerivedLowerShriek X P) ≫
      (Functor.leftUnitor (etaleDerivedLowerShriek X P)).hom)

/-- The first projection of `mayerVietorisToBiprod` recovers the whiskered map
to the `U`-summand. -/
theorem mayerVietorisToBiprod_fst :
    mayerVietorisToBiprod X P U V Λ ≫ biprod.fst =
      whiskerRight (mayerVietorisLowerShriekToLeft U V Λ)
        (etaleDerivedLowerShriek X P) :=
  sorry

/-- The second projection of `mayerVietorisToBiprod` recovers the whiskered map
to the `V`-summand. -/
theorem mayerVietorisToBiprod_snd :
    mayerVietorisToBiprod X P U V Λ ≫ biprod.snd =
      whiskerRight (mayerVietorisLowerShriekToRight U V Λ)
        (etaleDerivedLowerShriek X P) :=
  sorry

/-- The left inclusion into `mayerVietorisFromBiprod` is `Rf_!` of the counit
along `U`. -/
theorem mayerVietorisFromBiprod_inl :
    biprod.inl ≫ mayerVietorisFromBiprod X P U V Λ =
      whiskerRight (etaleDerivedExtensionByZeroAdjunction (U.ι) Λ).counit
          (etaleDerivedLowerShriek X P) ≫
        (Functor.leftUnitor (etaleDerivedLowerShriek X P)).hom :=
  sorry

/-- The right inclusion into `mayerVietorisFromBiprod` is `Rf_!` of the negative
of the counit along `V`. -/
theorem mayerVietorisFromBiprod_inr :
    biprod.inr ≫ mayerVietorisFromBiprod X P U V Λ =
      whiskerRight (-(etaleDerivedExtensionByZeroAdjunction (V.ι) Λ).counit)
          (etaleDerivedLowerShriek X P) ≫
        (Functor.leftUnitor (etaleDerivedLowerShriek X P)).hom :=
  sorry

/-- The two relative Mayer–Vietoris maps compose to zero. -/
theorem mayerVietorisToBiprod_comp_fromBiprod :
    mayerVietorisToBiprod X P U V Λ ≫ mayerVietorisFromBiprod X P U V Λ = 0 :=
  sorry

section PlusTorsion

variable [HasSheafCompose (smallEtaleTopology X.left)
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- Lemma 63.10.4: Let `f = X.hom` be a finite type separated morphism of
quasi-compact quasi-separated schemes, let `U` and `V` be quasi-compact opens of
`X.left` covering `X.left` (`U ⊔ V = ⊤`), and let `Λ` be a ring. Write
`a = U.ι ≫ X.hom`, `b = V.ι ≫ X.hom` and `c = (U ⊓ V).ι ≫ X.hom` for the
restrictions of `f`. For `K` in `D⁺_tors(X_étale, Λ)`, or in `D(X_étale, Λ)`
when `Λ` is torsion, there is a distinguished triangle
`Rc_!(K|_{U ∩ V}) ⟶ Ra_!(K|_U) ⊞ Rb_!(K|_V) ⟶ Rf_! K ⟶ Rc_!(K|_{U ∩ V})⟦1⟧`
in `D(Y_étale, Λ)`. The vertices are realized as
`Rf_!(j_{U ∩ V!}(K|_{U ∩ V}))`, `Rf_!(j_{U!}(K|_U)) ⊞ Rf_!(j_{V!}(K|_V))` and
`Rf_! K`, using `Rj_{W!} = j_{W!}` (Lemma 63.10.3) and
`Rf_! ∘ Rj_{W!} = R(f|_W)_!` (Lemma 63.9.2). The first two maps are
`mayerVietorisToBiprod` and `mayerVietorisFromBiprod`. -/
@[stacks 0GKN]
theorem mayerVietoris_triangle (hUV : U ⊔ V = ⊤) (K : EtaleDerived X.left Λ)
    (hK : AddMonoid.IsTorsion Λ ∨
      (etaleDerivedIsTorsion K ∧ ∃ n, DerivedCategory.IsGE K n)) :
    ∃ δ : (etaleDerivedLowerShriek X P).obj K ⟶
        ((etaleDerivedLowerShriek X P).obj
          ((etaleDerivedExtensionByZeroRestrict ((U ⊓ V).ι) Λ).obj K))⟦(1 : ℤ)⟧,
      Triangle.mk ((mayerVietorisToBiprod X P U V Λ).app K)
          ((mayerVietorisFromBiprod X P U V Λ).app K) δ ∈
        distTriang (EtaleDerived Y Λ) :=
  sorry

/-- Specialization of `mayerVietoris_triangle` to objects of
`D⁺_tors(X_étale, Λ)`. -/
theorem mayerVietoris_triangle_of_isGE_isTorsion (hUV : U ⊔ V = ⊤) {n : ℤ}
    (K : EtaleDerived X.left Λ) (h_tors : etaleDerivedIsTorsion K)
    [DerivedCategory.IsGE K n] :
    ∃ δ : (etaleDerivedLowerShriek X P).obj K ⟶
        ((etaleDerivedLowerShriek X P).obj
          ((etaleDerivedExtensionByZeroRestrict ((U ⊓ V).ι) Λ).obj K))⟦(1 : ℤ)⟧,
      Triangle.mk ((mayerVietorisToBiprod X P U V Λ).app K)
          ((mayerVietorisFromBiprod X P U V Λ).app K) δ ∈
        distTriang (EtaleDerived Y Λ) :=
  sorry

end PlusTorsion

/-- Specialization of `mayerVietoris_triangle` to a torsion coefficient ring,
valid on all of `D(X_étale, Λ)`. -/
theorem mayerVietoris_triangle_of_isTorsion (hΛ : AddMonoid.IsTorsion Λ)
    (hUV : U ⊔ V = ⊤) (K : EtaleDerived X.left Λ) :
    ∃ δ : (etaleDerivedLowerShriek X P).obj K ⟶
        ((etaleDerivedLowerShriek X P).obj
          ((etaleDerivedExtensionByZeroRestrict ((U ⊓ V).ι) Λ).obj K))⟦(1 : ℤ)⟧,
      Triangle.mk ((mayerVietorisToBiprod X P U V Λ).app K)
          ((mayerVietorisFromBiprod X P U V Λ).app K) δ ∈
        distTriang (EtaleDerived Y Λ) :=
  sorry

end etaleDerivedLowerShriek

end AlgebraicGeometry.Scheme.Etale

end
