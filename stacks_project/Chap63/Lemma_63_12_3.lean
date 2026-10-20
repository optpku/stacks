module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CompactSupport.DerivedComparison
import StacksCheckRecall

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
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} (ULift.{u} ℤ))]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} (ULift.{u} ℤ))]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [HasSheafify (Spec (CommRingCat.of k)).smallEtaleTopology
  (ModuleCat.{u} (ULift.{u} ℤ))]
variable [∀ U : (Spec (CommRingCat.of k)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of k)).smallEtaleTopology.over U)
    (ModuleCat.{u} (ULift.{u} ℤ))]
variable [HasDerivedCategory
  (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ULift.{u} ℤ),
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} (ULift.{u} ℤ))).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} (ULift.{u} ℤ)) (Spec (CommRingCat.of k)).smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} (ULift.{u} ℤ)) (Spec (CommRingCat.of k)).smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
    (ComplexShape.up ℤ))]
variable [HasDerivedCategory (ModuleCat.{u} (ULift.{u} ℤ))]
variable [((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
    (ModuleCat.{u} (ULift.{u} ℤ))).obj
    (op (globalEtale (Spec (CommRingCat.of k))))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
        (ModuleCat.{u} (ULift.{u} ℤ))).obj
      (op (globalEtale (Spec (CommRingCat.of k))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
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
variable [X.left.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toULiftIntModule]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toULiftIntModule]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]

/- Lemma 63.12.3: For a separated scheme of finite type over a field and a torsion
abelian étale sheaf, the two definitions of compactly supported degree-zero
cohomology agree through global sections of extension by zero. -/
@[stacks 0GK1] #check
  (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportDerivedEquiv P :
    ∀ (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
      IsLocallyTorsion F →
        globalSectionsCompactSupportSubgroup X F ≃+
          etaleDerivedCohomologyCompactSupport P 0
            ((DerivedCategory.singleFunctor
                (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))
                (0 : ℤ)).obj (etaleAbelianToIntModuleSheaf F)))

end AlgebraicGeometry.Scheme.Etale

end
