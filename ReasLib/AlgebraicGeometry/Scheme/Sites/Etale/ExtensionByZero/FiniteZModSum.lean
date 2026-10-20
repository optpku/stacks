module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}}

/-- The finite coproduct of extensions by zero of constant abelian sheaves with positive,
possibly varying `ZMod` coefficients on étale objects. -/
noncomputable def finiteZModExtensionByZeroSum {n : ℕ}
    (U : Fin n → X.Etale) (modulus : Fin n → ℕ)
    [hPos : ∀ i, NeZero (modulus i)]
    [hEtale : ∀ i, @Etale (U i).left X (U i).hom]
    [hKan : ∀ i, ∀ P : (U i).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleRestriction (U := (U i).left) (X := X) (U i).hom).op.HasLeftKanExtension P]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ i, HasWeakSheafify (U i).left.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasCoproduct fun i : Fin n ↦
      (abelianExtensionByZero (U := (U i).left) (X := X) (U i).hom).obj
        ((constantSheaf (U i).left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (.of (ULift.{u + 1} (ZMod (modulus i)))))] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ∐ fun i : Fin n ↦
    (abelianExtensionByZero (U := (U i).left) (X := X) (U i).hom).obj
      ((constantSheaf (U i).left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (.of (ULift.{u + 1} (ZMod (modulus i)))))

/-- A finite `ZMod` extension-by-zero sum is the coproduct of its constant-sheaf summands. -/
theorem finiteZModExtensionByZeroSum_def {n : ℕ}
    (U : Fin n → X.Etale) (modulus : Fin n → ℕ)
    [hPos : ∀ i, NeZero (modulus i)]
    [hEtale : ∀ i, @Etale (U i).left X (U i).hom]
    [hKan : ∀ i, ∀ P : (U i).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleRestriction (U := (U i).left) (X := X) (U i).hom).op.HasLeftKanExtension P]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ i, HasWeakSheafify (U i).left.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasCoproduct fun i : Fin n ↦
      (abelianExtensionByZero (U := (U i).left) (X := X) (U i).hom).obj
        ((constantSheaf (U i).left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (.of (ULift.{u + 1} (ZMod (modulus i)))))] :
    finiteZModExtensionByZeroSum U modulus =
      ∐ fun i : Fin n ↦
        (abelianExtensionByZero (U := (U i).left) (X := X) (U i).hom).obj
          ((constantSheaf (U i).left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (.of (ULift.{u + 1} (ZMod (modulus i))))) := sorry

end CategoryTheory.Sheaf
