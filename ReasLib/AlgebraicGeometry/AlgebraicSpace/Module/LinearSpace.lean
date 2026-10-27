/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SymmetricAlgebra
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Linear spaces of quasi-coherent modules on algebraic spaces

The linear space of a quasi-coherent module is the relative spectrum of its
symmetric algebra. Finite local freeness makes its projection flat,
quasi-separated, and locally of finite type; constant rank determines its
relative dimension.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The linear space of a quasi-coherent module is the relative spectrum of its
symmetric algebra. -/
def linearSpace (E : X.Modules) [E.IsQuasicoherent] : AlgebraicSpace S :=
  relativeSpec (SymmetricAlgebra.qcAlgebra E)

/-- The projection of the linear space of a quasi-coherent module to its base. -/
def linearSpaceπ (E : X.Modules) [E.IsQuasicoherent] : linearSpace E ⟶ X :=
  relativeSpecπ (SymmetricAlgebra.qcAlgebra E)

/-- The linear space is the relative spectrum of the symmetric algebra. -/
theorem linearSpace_eq_relativeSpec (E : X.Modules) [E.IsQuasicoherent] :
    linearSpace E = relativeSpec (SymmetricAlgebra.qcAlgebra E) :=
  rfl

/-- The linear-space projection is the structure morphism of the relative spectrum
of the symmetric algebra. -/
theorem linearSpaceπ_eq_relativeSpecπ (E : X.Modules) [E.IsQuasicoherent] :
    linearSpaceπ E = relativeSpecπ (SymmetricAlgebra.qcAlgebra E) :=
  rfl

/-- The linear-space projection of a finite locally free module is flat. -/
instance linearSpaceπ_flat (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] :
    Flat (linearSpaceπ E) :=
  sorry

/-- The linear-space projection of a module of constant finite local rank `r`
has relative dimension `r`. -/
instance linearSpaceπ_relativeDimension (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] :
    RelativeDimension (linearSpaceπ E) r :=
  sorry

/-- The linear-space projection of a finite locally free module is quasi-separated. -/
instance linearSpaceπ_quasiSeparated (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] :
    QuasiSeparated (linearSpaceπ E) :=
  sorry

/-- The linear-space projection of a finite locally free module is locally of finite type. -/
instance linearSpaceπ_locallyOfFiniteType (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] :
    LocallyOfFiniteType (linearSpaceπ E) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
