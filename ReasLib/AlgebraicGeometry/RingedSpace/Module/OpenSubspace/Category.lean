module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

@[expose] public section

/-!
# Module categories on open subspaces of a ringed space

This file owns the intrinsic category of modules on a restricted ringed space. Its categorical
instances are inherited directly from the ambient module-sheaf API. Restriction functors
themselves live in `OpenSubspace.Restriction`.
-/

open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The category of `𝒪_U`-modules on the open subspace `U` of `X`. -/
abbrev openSubspaceModuleCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  RingedSpace.Modules (X.restrict U.isOpenEmbedding)

end AlgebraicGeometry.RingedSpace
