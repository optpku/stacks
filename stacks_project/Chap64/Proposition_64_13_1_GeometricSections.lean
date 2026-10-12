/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap64.Definition_64_14_1_Comparison

/-!
# Geometric derived global sections over a general field

This leaf owns restriction of a derived étale `Λ`-module complex to the
geometric fibre `X_k̄` and the composite `RΓ(X_k̄, K|_{X_k̄})`, without a
finite-field or Frobenius hypothesis.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {Λ : Type u} [Ring Λ]
variable (X : SchemeOverField k)
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Abelian (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [Abelian (Sheaf (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (smallEtalePullback
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]

/-- Derived restriction of `K` to the geometric fibre `X_k̄`, as inverse image along
`FieldExtension.toSource`. -/
abbrev restrictionDerivedGeometricFibre
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    DerivedCategory (Sheaf (geometricFibre X).smallEtaleTopology (ModuleCat.{u} Λ)) :=
  (etaleModuleSheafPullback Λ
      (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).mapDerivedCategory.obj K

/-- Unfolding of `restrictionDerivedGeometricFibre` as `mapDerivedCategory` of étale
module sheaf pullback along `X_k̄ ⟶ X`. -/
theorem restrictionDerivedGeometricFibre_eq
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    restrictionDerivedGeometricFibre X K =
      (etaleModuleSheafPullback Λ
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).mapDerivedCategory.obj K :=
  sorry

/-- Derived global sections `RΓ(X_k̄, K|_{X_k̄})`. -/
abbrev rGammaGeometricFibre
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  (etaleModuleDerivedGamma Λ (geometricFibre X)).obj
    (restrictionDerivedGeometricFibre X K)

/-- Unfolding of `rGammaGeometricFibre` as derived étale global sections of
`restrictionDerivedGeometricFibre`. -/
theorem rGammaGeometricFibre_eq
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    rGammaGeometricFibre X K =
      (etaleModuleDerivedGamma Λ (geometricFibre X)).obj
        (restrictionDerivedGeometricFibre X K) :=
  sorry

end AlgebraicGeometry.SchemeOverField
