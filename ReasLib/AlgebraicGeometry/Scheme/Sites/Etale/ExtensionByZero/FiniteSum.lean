/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

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

end CategoryTheory.Sheaf
