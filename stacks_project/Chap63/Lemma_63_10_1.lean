/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (P : Compactification.Of Y X)
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

section CoproductComparison

variable {I : Type u} (K : I → EtaleDerived X.left Λ)
variable [HasCoproductsOfShape I (EtaleDerived X.left Λ)]
variable [HasCoproductsOfShape I (EtaleDerived Y Λ)]

/-- The canonical comparison `∐ Rf_! (K i) ⟶ Rf_! (∐ K)` induced by the
coproduct inclusions, where `Rf_!` is `etaleDerivedLowerShriek X P`. -/
noncomputable def etaleDerivedLowerShriekCoproductComparison :
    (∐ fun i ↦ (etaleDerivedLowerShriek X P).obj (K i)) ⟶
      (etaleDerivedLowerShriek X P).obj (∐ K) :=
  Sigma.desc fun i ↦ (etaleDerivedLowerShriek X P).map (Sigma.ι K i)

/-- The comparison morphism recovers `Rf_!` of the `i`-th coproduct inclusion. -/
theorem etaleDerivedLowerShriekCoproductComparison_comp_ι (i : I) :
    Sigma.ι (fun j ↦ (etaleDerivedLowerShriek X P).obj (K j)) i ≫
        etaleDerivedLowerShriekCoproductComparison X P K =
      (etaleDerivedLowerShriek X P).map (Sigma.ι K i) := sorry

/-- Lemma 63.10.1 (1): if `f = X.hom` is a finite type separated morphism of
quasi-compact quasi-separated schemes and `K i` is a family in
`D⁺_tors(X_étale, Λ)`, uniformly bounded below, then `Rf_!` commutes with
direct sums. If `H^n(K i) = 0` for all `n < a` (equivalently
`DerivedCategory.IsGE (K i) a`) and each `K i` has torsion cohomology sheaves
(`etaleDerivedIsTorsion`), then the comparison
`∐ Rf_! (K i) ⟶ Rf_! (∐ K)` is an isomorphism in `D(Y_étale, Λ)`. -/
@[stacks 0G29]
theorem etaleDerivedLowerShriek_preservesCoproduct
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [HasSheafCompose X.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (a : ℤ) (hK : ∀ i, DerivedCategory.IsGE (K i) a)
    (h_tors : ∀ i, etaleDerivedIsTorsion (K i)) :
    IsIso (etaleDerivedLowerShriekCoproductComparison X P K) := sorry

end CoproductComparison

/-- Lemma 63.10.1 (2): if `Λ` is a torsion ring (`AddMonoid.IsTorsion Λ`) and
`f = X.hom` is a finite type separated morphism of quasi-compact
quasi-separated schemes, then
`Rf_! = etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ`
commutes with direct sums. -/
@[stacks 0G29]
theorem etaleDerivedLowerShriek_preservesCoproducts
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (hΛ : AddMonoid.IsTorsion Λ) (I : Type u)
    [HasCoproductsOfShape I (EtaleDerived X.left Λ)]
    [HasCoproductsOfShape I (EtaleDerived Y Λ)] :
    PreservesColimitsOfShape (Discrete I)
      (etaleDerivedLowerShriek X P :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) := sorry

end AlgebraicGeometry.Scheme.Etale

end
