/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.Lemma_63_10_5_Triangle
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative complementary triangle for derived étale lower shriek
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Pretriangulated
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) (P : Compactification.Of Y X)
variable {Z : Scheme.{u}} (i : Z ⟶ X.left) (Λ : Type u) [CommRing Λ]
variable [IsClosedImmersion i]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [CompactSpace (closedImmersionComplement i).toScheme]
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
variable [∀ F : (closedImmersionComplement i).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (closedImmersionComplement i).ι).op.HasLeftKanExtension F]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback i).op.HasLeftKanExtension G]
variable [HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify
  (closedImmersionComplement i).toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Abelian (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [Abelian
  (Sheaf (closedImmersionComplement i).toScheme.smallEtaleTopology
    (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory
  (Sheaf (closedImmersionComplement i).toScheme.smallEtaleTopology
    (ModuleCat.{u} Λ))]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : (closedImmersionComplement i).toScheme.Etale,
  HasWeakSheafify
    ((closedImmersionComplement i).toScheme.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [(etaleRestrictionSheaf (closedImmersionComplement i).ι
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (closedImmersionComplement i).ι
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{u} Λ))]
variable [((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
  ((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology)]
variable [((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
  ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology)]
variable [(moduleClosedOpenLower i Λ).Additive]
variable [(moduleClosedOpenClosed i Λ).Additive]
variable [PreservesFiniteLimits (moduleClosedOpenLower i Λ)]
variable [PreservesFiniteColimits (moduleClosedOpenLower i Λ)]
variable [PreservesFiniteLimits (moduleClosedOpenClosed i Λ)]
variable [PreservesFiniteColimits (moduleClosedOpenClosed i Λ)]
variable [(etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).CommShift ℤ]
variable [(etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).IsTriangulated]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- Lemma 63.10.5: Let `f = X.hom : X.left ⟶ Y` be a finite type separated
morphism of quasi-compact quasi-separated schemes, and let `i : Z ⟶ X.left` be
a closed immersion whose open complement `U = closedImmersionComplement i` is
quasi-compact. Write `g = U.ι ≫ X.hom` and `h = i ≫ X.hom` for the restrictions
of `f`. Let `Λ` be a ring. For `K` in `D⁺_tors(X_étale, Λ)`, or in
`D(X_étale, Λ)` when `Λ` is torsion, the image under `Rf_!` of the complementary
closed/open triangle is distinguished in `D(Y_étale, Λ)`:
`Rg_!(K|_U) ⟶ Rf_! K ⟶ Rh_!(K|_Z) ⟶ Rg_!(K|_U)⟦1⟧`.
The vertices are realized as `Rf_!(j_!(K|_U))`, `Rf_! K` and `Rf_!(i_* i⁻¹ K)`,
using `Rj_! = j_!` and `Ri_! = i_*` (Lemma 63.10.3) and
`Rf_! ∘ Rj_! = Rg_!`, `Rf_! ∘ Ri_!` (Lemma 63.9.2). -/
@[stacks 0GKP]
theorem etaleDerivedLowerShriek_closedOpen_triangle_distinguished
    (K : EtaleDerived X.left Λ)
    (hK : AddMonoid.IsTorsion Λ ∨
      (etaleDerivedIsTorsion K ∧ ∃ n, DerivedCategory.IsGE K n)) :
    etaleDerivedLowerShriekClosedOpenTriangle X P i Λ K ∈
      distTriang (EtaleDerived Y Λ) :=
  sorry

/-- Specialization of `etaleDerivedLowerShriek_closedOpen_triangle_distinguished`
to a torsion coefficient ring, valid on all of `D(X_étale, Λ)`. -/
theorem etaleDerivedLowerShriek_closedOpen_triangle_distinguished_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) (K : EtaleDerived X.left Λ) :
    etaleDerivedLowerShriekClosedOpenTriangle X P i Λ K ∈
      distTriang (EtaleDerived Y Λ) :=
  sorry

/-- Specialization of `etaleDerivedLowerShriek_closedOpen_triangle_distinguished`
to objects of `D⁺_tors(X_étale, Λ)`. -/
theorem etaleDerivedLowerShriek_closedOpen_triangle_distinguished_of_isGE_isTorsion
    {n : ℤ} (K : EtaleDerived X.left Λ) (h_tors : etaleDerivedIsTorsion K)
    [DerivedCategory.IsGE K n] :
    etaleDerivedLowerShriekClosedOpenTriangle X P i Λ K ∈
      distTriang (EtaleDerived Y Λ) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
