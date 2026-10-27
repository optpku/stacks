/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SymmetricAlgebra

/-! # Associated linear spaces of quasi-coherent modules on algebraic spaces -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The associated linear space of a quasi-coherent module is the relative spectrum
of its symmetric algebra. -/
noncomputable def associatedVectorBundle (F : X.Modules) [F.IsQuasicoherent] :
    AlgebraicSpace S :=
  relativeSpec (SymmetricAlgebra.qcAlgebra F)

/-- The projection of the associated linear space of a quasi-coherent module. -/
noncomputable def associatedVectorBundleπ (F : X.Modules) [F.IsQuasicoherent] :
    associatedVectorBundle F ⟶ X :=
  relativeSpecπ (SymmetricAlgebra.qcAlgebra F)

/-- The associated linear space is the relative spectrum of the symmetric algebra. -/
theorem associatedVectorBundle_eq_relativeSpec (F : X.Modules) [F.IsQuasicoherent] :
    associatedVectorBundle F = relativeSpec (SymmetricAlgebra.qcAlgebra F) := rfl

/-- The associated linear-space projection is the symmetric-algebra relative-spectrum
projection. -/
theorem associatedVectorBundleπ_eq_relativeSpecπ (F : X.Modules) [F.IsQuasicoherent] :
    associatedVectorBundleπ F = relativeSpecπ (SymmetricAlgebra.qcAlgebra F) := rfl

end AlgebraicGeometry.AlgebraicSpace
