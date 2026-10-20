/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricAlgebra.CommRing
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricAlgebra.Properties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Symmetric
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic

/-!
# Symmetric algebras of quasi-coherent module sheaves

This file packages the symmetric algebra of a quasi-coherent module sheaf as an explicit
quasi-coherent algebra over the structure sheaf of a scheme.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SymmetricAlgebra

variable {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsQuasicoherent]

/-- The commutative-ring sheaf obtained by sheafifying the sectionwise symmetric-algebra
presheaf of `ℱ`. -/
noncomputable abbrev sheaf :
    CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology S) CommRingCat.{u}).obj
    (PresheafOfModules.SymmetricAlgebra.commRingPresheaf S.presheaf ℱ.val)

/-- The canonical structure map from `𝒪_S` to the symmetric-algebra sheaf of `ℱ`. -/
noncomputable abbrev structureMap : S.sheaf ⟶ sheaf ℱ :=
  Sheaf.homEquiv.symm
    (PresheafOfModules.SymmetricAlgebra.commRingUnit S.presheaf ℱ.val ≫
      toSheafify (Opens.grothendieckTopology S)
        (PresheafOfModules.SymmetricAlgebra.commRingPresheaf S.presheaf ℱ.val))

/-- The symmetric-algebra sheaf of `ℱ`, regarded as an algebra object under `𝒪_S`. -/
noncomputable def under : Under S.sheaf :=
  Under.mk (structureMap ℱ)

/-- The `𝒪_S`-module underlying the symmetric-algebra object `under ℱ`. -/
noncomputable abbrev underlyingModule : S.Modules :=
  (SheafOfModules.RingedSite.restrictionAlong (under ℱ).hom).obj
    (SheafOfModules.RingedSite.unitModule (Opens.grothendieckTopology S) (under ℱ).right)

/-- The module underlying the explicit symmetric-algebra object is the canonical symmetric
algebra sheaf `Symm(ℱ)`. -/
theorem underlyingModule_eq : underlyingModule ℱ = Symm(ℱ) := sorry

/-- The module underlying the symmetric-algebra object of a quasi-coherent module is
quasi-coherent. -/
theorem underlyingModule_isQuasicoherent : (underlyingModule ℱ).IsQuasicoherent := sorry

/-- The symmetric algebra of `ℱ` as a quasi-coherent `𝒪_S`-algebra. -/
noncomputable def qcAlgebra : S.QcAlgebraUnder :=
  ⟨under ℱ, underlyingModule_isQuasicoherent ℱ⟩

end AlgebraicGeometry.Scheme.SymmetricAlgebra
