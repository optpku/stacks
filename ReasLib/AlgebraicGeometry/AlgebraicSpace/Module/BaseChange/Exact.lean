module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exact sequences under base change of modules on algebraic spaces

In a right exact sequence of quasi-coherent modules, the second morphism becomes an
isomorphism after base change precisely when the first morphism becomes zero.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 ℋ : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] [ℋ.IsQuasicoherent]

/-- For a right exact sequence `ℱ ⟶ 𝒢 ⟶ ℋ ⟶ 0` of quasi-coherent modules on an
algebraic space, the base change of the second morphism to a scheme over the base is an
isomorphism if and only if the base change of the first morphism is zero. -/
@[stacks 0CVM]
theorem baseChangeMap_isIso_iff_zero_of_exact (u : ℱ ⟶ 𝒢) (v : 𝒢 ⟶ ℋ)
    (h_comp : u ≫ v = 0) (h_exact : (ShortComplex.mk u v h_comp).Exact)
    [Epi v] (T : SchemeOver B) :
    IsIso (baseChangeMap f T.hom v) ↔ baseChangeMap f T.hom u = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
