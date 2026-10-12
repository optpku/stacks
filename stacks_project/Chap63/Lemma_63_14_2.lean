/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.KrullDimension
public import stacks_project.Chap59.Definition_59_71_1
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructible cohomology of compact-support pushforward of a constant sheaf

If `S` is Noetherian affine of finite dimension and `X.hom : X.left ⟶ S` is
separated, affine, and smooth of relative dimension `1`, then `Rf_!` of a
constant sheaf of a finite module over a Noetherian torsion ring has
constructible cohomology.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}} (X : Over S)
variable [IsAffine S] [IsNoetherian S]
variable [IsSeparated X.hom] [IsAffineHom X.hom]
variable [SmoothOfRelativeDimension 1 X.hom] [Scheme.Hom.FiniteType X.hom]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable {M : Type u} [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]
variable (P : Compactification.Of S X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : S.Etale,
  HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) S.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) S.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (V : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ S) (G : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]

/-- Lemma 63.14.2: if `S` is a Noetherian affine scheme of finite dimension,
`f = X.hom : X.left ⟶ S` is separated, affine, and smooth of relative
dimension `1`, `Λ` is a Noetherian torsion ring, and `M` is a finite
`Λ`-module, then `Rf_!` of the constant étale sheaf of `M` has constructible
cohomology sheaves. -/
@[stacks 0GKX]
theorem etaleDerivedLowerShriek_constantModule_cohomology_isConstructible
    (hΛ : AddMonoid.IsTorsion Λ) (hdim : topologicalKrullDim S < ⊤) :
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            S.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek X P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
          ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (.of Λ M)))) :=
  sorry

/-- Each homology sheaf of `Rf_!` of the constant étale sheaf of `M` is a
constructible étale sheaf of `Λ`-modules on `S`. -/
theorem etaleDerivedLowerShriek_constantModule_homology_isConstructibleEtaleModule
    (hΛ : AddMonoid.IsTorsion Λ) (hdim : topologicalKrullDim S < ⊤) (n : ℤ) :
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          S.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
        ((etaleDerivedLowerShriek X P).obj
          ((DerivedCategory.singleFunctor
              (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
            ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
              (.of Λ M))))) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
