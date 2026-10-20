/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} {Λ : Type w} [Ring Λ]

/-- The finite coproduct of extensions by zero of the constant sheaf on the regular module.
-/
noncomputable def finiteExtensionByZeroSum {n : ℕ}
    (U : Fin n → Scheme.{u}) (j : ∀ i, U i ⟶ X)
    [h : ∀ i, Etale (j i)]
    [hKan : ∀ i, ∀ F : (U i).Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction (j i)).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ i, HasWeakSheafify (U i).smallEtaleTopology (ModuleCat.{w} Λ)]
    [HasCoproduct fun i : Fin n ↦
      (moduleExtensionByZero (j i)).obj
        ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{w} Λ)).obj (.of Λ Λ))] :
    Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) :=
  ∐ fun i : Fin n ↦
    (moduleExtensionByZero (j i)).obj
      ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{w} Λ)).obj (.of Λ Λ))

/-- The finite extension-by-zero sum is the coproduct of its constant-sheaf summands.
-/
theorem finiteExtensionByZeroSum_def {n : ℕ}
    (U : Fin n → Scheme.{u}) (j : ∀ i, U i ⟶ X)
    [h : ∀ i, Etale (j i)]
    [hKan : ∀ i, ∀ F : (U i).Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction (j i)).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ i, HasWeakSheafify (U i).smallEtaleTopology (ModuleCat.{w} Λ)]
    [HasCoproduct fun i : Fin n ↦
      (moduleExtensionByZero (j i)).obj
        ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{w} Λ)).obj (.of Λ Λ))] :
    finiteExtensionByZeroSum U j =
      ∐ fun i : Fin n ↦
        (moduleExtensionByZero (j i)).obj
          ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{w} Λ)).obj
            (.of Λ Λ)) := sorry

variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]

/-- A module sheaf is an affine étale extension-by-zero sum if it is isomorphic to a
finite coproduct of regular constant module sheaves extended by zero from affine étale
schemes. The empty coproduct is allowed. -/
def IsFiniteAffineEtaleExtensionByZeroSum
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) : Prop :=
  ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (j : ∀ i, U i ⟶ X)
    (hEtale : ∀ i, Etale (j i))
    (hAffine : ∀ i, IsAffine (U i))
    (hKan : ∀ i, ∀ G : (U i).Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (@etaleRestriction (U i) X (j i) (hEtale i)).op.HasLeftKanExtension G)
    (hSheafify : ∀ i, HasWeakSheafify (U i).smallEtaleTopology (ModuleCat.{w} Λ))
    (hCoproduct : HasCoproduct fun i : Fin n ↦
      (moduleExtensionByZero (j i)).obj
        ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{w} Λ)).obj (.of Λ Λ))),
    Nonempty (F ≅ finiteExtensionByZeroSum U j)

/-- The affine étale extension-by-zero sum predicate is equivalent to the existence of
affine étale summands and an isomorphism with their finite coproduct. -/
theorem isFiniteAffineEtaleExtensionByZeroSum_iff
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) :
    IsFiniteAffineEtaleExtensionByZeroSum F ↔
      ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (j : ∀ i, U i ⟶ X)
        (hEtale : ∀ i, Etale (j i))
        (hAffine : ∀ i, IsAffine (U i))
        (hKan : ∀ i, ∀ G : (U i).Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
          (@etaleRestriction (U i) X (j i) (hEtale i)).op.HasLeftKanExtension G)
        (hSheafify : ∀ i,
          HasWeakSheafify (U i).smallEtaleTopology (ModuleCat.{w} Λ))
        (hCoproduct : HasCoproduct fun i : Fin n ↦
          (moduleExtensionByZero (j i)).obj
            ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{w} Λ)).obj (.of Λ Λ))),
        Nonempty (F ≅ finiteExtensionByZeroSum U j) := Iff.rfl

end CategoryTheory.Sheaf
