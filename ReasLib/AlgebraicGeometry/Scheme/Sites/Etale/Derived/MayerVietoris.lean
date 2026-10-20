module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ExtensionByZero


/-!
# Mayer–Vietoris maps for étale derived extension by zero

This module packages the two canonical maps in the lower-shriek Mayer–Vietoris
triangle on `D(X_étale, Λ)` associated to a pair of opens.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open Functor

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

section NestedOpens

variable {X : Scheme.{u}} {W U : X.Opens} (h : W ≤ U)
variable (Λ : Type v) [CommRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ V : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasWeakSheafify U.toScheme.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ V : U.toScheme.Etale,
  HasWeakSheafify (U.toScheme.smallEtaleTopology.over V) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasWeakSheafify W.toScheme.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ V : W.toScheme.Etale,
  HasWeakSheafify (W.toScheme.smallEtaleTopology.over V) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf W.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf W.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ F : W.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction (W.ι)).op.HasLeftKanExtension F]
variable [∀ F : U.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction (U.ι)).op.HasLeftKanExtension F]
variable [∀ F : W.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction ((X.homOfLE h))).op.HasLeftKanExtension F]
variable [(etaleRestrictionSheaf (W.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf (W.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf (W.ι) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (W.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (W.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (W.ι) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ) ⋙ etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ) ⋙ etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]

/-- Canonical identification of `j_{W!}((-) |_W)` with the composite through an
intermediate open `U` containing `W`. -/
noncomputable def etaleDerivedExtensionByZeroRestrict_le :
    etaleDerivedExtensionByZeroRestrict (W.ι) Λ ≅
      etaleDerivedRestriction (U.ι) Λ ⋙
        (etaleDerivedRestriction ((X.homOfLE h)) Λ ⋙
          etaleDerivedExtensionByZero ((X.homOfLE h)) Λ) ⋙
        etaleDerivedExtensionByZero (U.ι) Λ :=
  Functor.isoWhiskerRight (etaleDerivedRestriction_comp h Λ)
      (etaleDerivedExtensionByZero (W.ι) Λ) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleDerivedRestriction (U.ι) Λ)
      (Functor.isoWhiskerLeft (etaleDerivedRestriction ((X.homOfLE h)) Λ)
          (etaleDerivedExtensionByZero_comp h Λ).symm ≪≫
        (Functor.associator _ _ _).symm)

/-- The functoriality map `j_{W!}((-) |_W) ⟶ j_{U!}((-) |_U)` along an inclusion
of opens `W ≤ U`, obtained from the inner open-immersion counit. -/
noncomputable def mayerVietorisLowerShriekToOfLE :
    etaleDerivedExtensionByZeroRestrict (W.ι) Λ ⟶
      etaleDerivedExtensionByZeroRestrict (U.ι) Λ :=
  (etaleDerivedExtensionByZeroRestrict_le h Λ).hom ≫
    whiskerLeft (etaleDerivedRestriction (U.ι) Λ)
      (whiskerRight (etaleDerivedExtensionByZeroAdjunction (X.homOfLE h) Λ).counit
        (etaleDerivedExtensionByZero (U.ι) Λ)) ≫
    whiskerLeft (etaleDerivedRestriction (U.ι) Λ) (Functor.leftUnitor _).hom

end NestedOpens

section TwoOpens

variable {X : Scheme.{u}} (U V : X.Opens)
variable (Λ : Type v) [CommRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ W : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over W) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasWeakSheafify U.toScheme.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ W : U.toScheme.Etale,
  HasWeakSheafify (U.toScheme.smallEtaleTopology.over W) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasWeakSheafify V.toScheme.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ W : V.toScheme.Etale,
  HasWeakSheafify (V.toScheme.smallEtaleTopology.over W) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasWeakSheafify (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ W : (U ⊓ V).toScheme.Etale,
  HasWeakSheafify ((U ⊓ V).toScheme.smallEtaleTopology.over W) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory
  (Sheaf (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ F : U.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction (U.ι)).op.HasLeftKanExtension F]
variable [∀ F : V.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction (V.ι)).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction ((U ⊓ V).ι)).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction ((X.homOfLE (inf_le_left : U ⊓ V ≤ U)))).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction ((X.homOfLE (inf_le_right : U ⊓ V ≤ V)))).op.HasLeftKanExtension F]
variable [(etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf ((U ⊓ V).ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf ((U ⊓ V).ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf ((U ⊓ V).ι) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf ((X.homOfLE (inf_le_left : U ⊓ V ≤ U)))
    (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf ((X.homOfLE (inf_le_left : U ⊓ V ≤ U))) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf ((X.homOfLE (inf_le_left : U ⊓ V ≤ U))) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf ((X.homOfLE (inf_le_right : U ⊓ V ≤ V)))
    (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf ((X.homOfLE (inf_le_right : U ⊓ V ≤ V))) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf ((X.homOfLE (inf_le_right : U ⊓ V ≤ V))) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero ((U ⊓ V).ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero ((U ⊓ V).ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero ((U ⊓ V).ι) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE (inf_le_left : U ⊓ V ≤ U)))
      (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE (inf_le_left : U ⊓ V ≤ U)))
      (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE (inf_le_left : U ⊓ V ≤ U)))
      (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ))]

/-- The functoriality map from the intersection open to the first open. -/
noncomputable def mayerVietorisLowerShriekToLeft :
    etaleDerivedExtensionByZeroRestrict ((U ⊓ V).ι) Λ ⟶
      etaleDerivedExtensionByZeroRestrict (U.ι) Λ :=
  mayerVietorisLowerShriekToOfLE (inf_le_left : U ⊓ V ≤ U) Λ

/-- The functoriality map from the intersection open to the second open. -/
noncomputable def mayerVietorisLowerShriekToRight :
    etaleDerivedExtensionByZeroRestrict ((U ⊓ V).ι) Λ ⟶
      etaleDerivedExtensionByZeroRestrict (V.ι) Λ :=
  mayerVietorisLowerShriekToOfLE (inf_le_right : U ⊓ V ≤ V) Λ

/-- The first Mayer–Vietoris map
`j_{U ∩ V!}((-) |_{U ∩ V}) ⟶ j_{U!}((-) |_U) ⊞ j_{V!}((-) |_V)`. -/
noncomputable def mayerVietorisLowerShriekToBiprod :
    etaleDerivedExtensionByZeroRestrict ((U ⊓ V).ι) Λ ⟶
      etaleDerivedExtensionByZeroRestrict (U.ι) Λ ⊞
        etaleDerivedExtensionByZeroRestrict (V.ι) Λ :=
  biprod.lift (mayerVietorisLowerShriekToLeft U V Λ)
    (mayerVietorisLowerShriekToRight U V Λ)

/-- The second Mayer–Vietoris map
`j_{U!}((-) |_U) ⊞ j_{V!}((-) |_V) ⟶ 𝟭`, with a minus on the `V`-component. -/
noncomputable def mayerVietorisLowerShriekFromBiprod :
    etaleDerivedExtensionByZeroRestrict (U.ι) Λ ⊞
        etaleDerivedExtensionByZeroRestrict (V.ι) Λ ⟶
      𝟭 (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) :=
  biprod.desc (etaleDerivedExtensionByZeroAdjunction (U.ι) Λ).counit
    (-(etaleDerivedExtensionByZeroAdjunction (V.ι) Λ).counit)

/-- The first projection of `mayerVietorisLowerShriekToBiprod` is the map to the
left summand. -/
theorem mayerVietorisLowerShriekToBiprod_fst :
    mayerVietorisLowerShriekToBiprod U V Λ ≫ biprod.fst =
      mayerVietorisLowerShriekToLeft U V Λ :=
  sorry

/-- The second projection of `mayerVietorisLowerShriekToBiprod` is the map to the
right summand. -/
theorem mayerVietorisLowerShriekToBiprod_snd :
    mayerVietorisLowerShriekToBiprod U V Λ ≫ biprod.snd =
      mayerVietorisLowerShriekToRight U V Λ :=
  sorry

/-- The left inclusion into `mayerVietorisLowerShriekFromBiprod` is the counit
along `U`. -/
theorem mayerVietorisLowerShriekFromBiprod_inl :
    biprod.inl ≫ mayerVietorisLowerShriekFromBiprod U V Λ =
      (etaleDerivedExtensionByZeroAdjunction (U.ι) Λ).counit :=
  sorry

/-- The right inclusion into `mayerVietorisLowerShriekFromBiprod` is the negative
of the counit along `V`. -/
theorem mayerVietorisLowerShriekFromBiprod_inr :
    biprod.inr ≫ mayerVietorisLowerShriekFromBiprod U V Λ =
      -(etaleDerivedExtensionByZeroAdjunction (V.ι) Λ).counit :=
  sorry

/-- The two Mayer–Vietoris maps compose to zero. -/
theorem mayerVietorisLowerShriekToBiprod_comp_fromBiprod :
    mayerVietorisLowerShriekToBiprod U V Λ ≫
        mayerVietorisLowerShriekFromBiprod U V Λ = 0 :=
  sorry

/-- A Mayer–Vietoris cover by two opens yields a distinguished triangle in the
derived category of étale sheaves. -/
theorem etaleDerived_mayerVietoris_lowerShriek_triangle (hUV : U ⊔ V = ⊤) :
    ∃ δ : 𝟭 (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) ⟶
        etaleDerivedExtensionByZeroRestrict ((U ⊓ V).ι) Λ ⋙
          shiftFunctor (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) (1 : ℤ),
      ∀ K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)),
        Triangle.mk
            ((mayerVietorisLowerShriekToBiprod U V Λ).app K)
            ((mayerVietorisLowerShriekFromBiprod U V Λ).app K)
            (δ.app K) ∈ distTriang (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) :=
  sorry

/-- The objectwise form of the distinguished triangle supplied by the
Mayer–Vietoris construction. -/
theorem etaleDerivedMayerVietorisLowerShriekTriangle
    (hUV : U ⊔ V = ⊤) (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) :
    ∃ δ : K ⟶
        ((etaleDerivedExtensionByZeroRestrict ((U ⊓ V).ι) Λ).obj K)⟦(1 : ℤ)⟧,
      Triangle.mk
          ((mayerVietorisLowerShriekToBiprod U V Λ).app K)
          ((mayerVietorisLowerShriekFromBiprod U V Λ).app K)
          δ ∈ distTriang (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) :=
  sorry

end TwoOpens

end AlgebraicGeometry.Scheme.Etale

end
