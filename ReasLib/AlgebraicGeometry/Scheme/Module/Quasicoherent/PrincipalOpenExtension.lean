module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Opens

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Every quasi-coherent module on a principal open subscheme of `Spec R` is isomorphic
to the restriction of a quasi-coherent module on `Spec R`. -/
theorem exists_isQuasicoherent_restrict_basicOpen {R : CommRingCat.{u}} (f : R)
    (𝒢 : ((Spec R).basicOpen ((ΓSpecIso R).inv f)).toScheme.Modules) [𝒢.IsQuasicoherent] :
    ∃ ℱ : (Spec R).Modules, ℱ.IsQuasicoherent ∧
      Nonempty (ℱ.restrict (((Spec R).basicOpen ((ΓSpecIso R).inv f)).ι) ≅ 𝒢) := sorry

end AlgebraicGeometry.Scheme.Modules
