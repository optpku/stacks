/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Data.List.TFAE

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

/-- Cardinal rank of a module sheaf on an integral scheme: vector-space
dimension of its stalk at the generic point over the function field.
The generic stalk ring is a field, canonically its own residue field. -/
noncomputable def genericRank (F : X.Modules) : Cardinal.{u} :=
  Module.rank X.functionField
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf (genericPoint X))

/-- Generic rank can be checked on every nonempty affine open, or on one
nonempty affine open. -/
theorem genericRank_affine_tfae (F : X.Modules) [F.IsQuasicoherent] (r : Cardinal.{u}) :
    List.TFAE [
      genericRank F = r,
      ∀ U : X.affineOpens, Nonempty (U : X.Opens) →
        Module.rank Γ(X, U) Γ(F, U) = r,
      ∃ U : X.affineOpens, Nonempty (U : X.Opens) ∧
        Module.rank Γ(X, U) Γ(F, U) = r
    ] := sorry

/-- Generic cardinal rank is additive in a short exact sequence of
quasi-coherent modules. -/
theorem genericRank_additive (S : ShortComplex X.Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hS : S.ShortExact) :
    genericRank S.X₂ = genericRank S.X₁ + genericRank S.X₃ := sorry

/-- Tensor products of quasi-coherent modules multiply cardinal generic
ranks; no finite rank assumption is made. -/
theorem genericRank_tensor (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    genericRank (F ⊗ G) = genericRank F * genericRank G := sorry

/-- Internal sheaf Hom multiplies cardinal generic ranks when its source is
finitely presented. The target can have arbitrary cardinal rank. -/
theorem genericRank_internalHom (F G : X.Modules) [F.IsFinitePresentation]
    [G.IsQuasicoherent] :
    genericRank (internalHom F G) = genericRank F * genericRank G := sorry

/-- A finite-type quasi-coherent module has finite generic rank and is
actually free of that rank on a nonempty open subscheme. -/
theorem exists_nonempty_open_free_of_finiteType (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ r : ℕ, genericRank F = (r : Cardinal) ∧
      ∃ U : X.Opens, Nonempty U ∧
        Nonempty (F.restrict U.ι ≅ (SheafOfModules.free (ULift.{u} (Fin r)) : U.toScheme.Modules)) := sorry

end AlgebraicGeometry.Scheme.Modules
