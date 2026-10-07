module

public import stacks_project.Chap63.Lemma_63_12_3_Comparison

/-!
# Agreement of underived and derived compactly supported H^0

Lemma 63.12.3: for a separated finite-type scheme `X` over a field `k` and a
torsion abelian sheaf `F`, the group `H^0_c(X, F)` of Definition 63.3.7 agrees
with the group `H^0_c(X, F)` of Definition 63.12.1.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {k : Type u} [Field k]
variable {X : SchemeOverField k}
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [IsOpenImmersion (Compactification.Of.ι P)]
variable [IsProper P.obj.right.hom]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} ULiftInt)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} ULiftInt)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))]
variable [HasSheafify (Spec (CommRingCat.of k)).smallEtaleTopology
  (ModuleCat.{u} ULiftInt)]
variable [∀ U : (Spec (CommRingCat.of k)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of k)).smallEtaleTopology.over U)
    (ModuleCat.{u} ULiftInt)]
variable [HasDerivedCategory
  (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} ULiftInt))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} ULiftInt,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} ULiftInt)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} ULiftInt))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} ULiftInt))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} ULiftInt) (Spec (CommRingCat.of k)).smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} ULiftInt) (Spec (CommRingCat.of k)).smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} ULiftInt))
    (ComplexShape.up ℤ))]
variable [HasDerivedCategory (ModuleCat.{u} ULiftInt)]
variable [((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
    (ModuleCat.{u} ULiftInt)).obj
    (op (globalEtale (Spec (CommRingCat.of k))))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
        (ModuleCat.{u} ULiftInt)).obj
      (op (globalEtale (Spec (CommRingCat.of k))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} ULiftInt))
    (ComplexShape.up ℤ))]
variable [CompactSpace (Spec (CommRingCat.of k))]
variable [QuasiSeparatedSpace (Spec (CommRingCat.of k))]
variable [HasWeakSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [∀ G : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous
    AddCommGrpCat.{u} P.obj.right.left.smallEtaleTopology
    X.left.smallEtaleTopology).IsRightAdjoint]
variable [X.left.smallEtaleTopology.HasSheafCompose addCommGrpToULiftIntModule]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose addCommGrpToULiftIntModule]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} ULiftInt) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} ULiftInt) AddCommGrpCat.{u})]

/-- Lemma 63.12.3: Let `X` be a separated scheme of finite type over a field
`k`. If `F` is a torsion abelian sheaf, then the abelian group `H^0_c(X, F)`
defined in Definition 63.3.7 agrees with the abelian group `H^0_c(X, F)`
defined in Definition 63.12.1. -/
@[stacks 0GK1]
def globalSectionsCompactSupportDerivedEquiv
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) :
    globalSectionsCompactSupportSubgroup X F ≃+
      etaleDerivedCohomologyCompactSupport P 0
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)) (0 : ℤ)).obj
          (etaleAbelianToIntModuleSheaf F)) :=
  AddEquiv.ofBijective (globalSectionsCompactSupportDerivedHom P F hF)
    (globalSectionsCompactSupportDerivedHom_bijective P F hF)

/-- The underlying map of `globalSectionsCompactSupportDerivedEquiv` is
`globalSectionsCompactSupportDerivedHom`. -/
theorem globalSectionsCompactSupportDerivedEquiv_apply
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F)
    (σ : globalSectionsCompactSupportSubgroup X F) :
    globalSectionsCompactSupportDerivedEquiv P F hF σ =
      globalSectionsCompactSupportDerivedHom P F hF σ :=
  sorry

/-- The identification of underived and derived `H^0_c` is the compactification
comparison of Lemma 63.3.10, followed by coefficient conversion of `j_! F`
and the derived identification of `Γ(X̄, j_! F)` with derived `H^0_c`. -/
theorem globalSectionsCompactSupportDerivedEquiv_comp
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) :
    (globalSectionsCompactSupportDerivedEquiv P F hF).toAddMonoidHom =
      (etaleDerivedCohomologyCompactSupportZeroAddHom P
            (etaleAbelianToIntModuleSheaf F)).comp
        ((etaleExtensionByZeroAbelianToModuleSections P F).comp
          (globalSectionsCompactSupportCompactifyGlobalEquiv P.obj.hom F).toAddMonoidHom) :=
  sorry

/-- A torsion abelian sheaf remains torsion after conversion to a sheaf of
`ℤ`-modules and placement in degree zero in the derived category. -/
theorem etaleAbelianToIntModuleSheaf_single_isTorsion
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) :
    etaleDerivedIsTorsion
      ((DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} ULiftInt)) (0 : ℤ)).obj
        (etaleAbelianToIntModuleSheaf F)) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
