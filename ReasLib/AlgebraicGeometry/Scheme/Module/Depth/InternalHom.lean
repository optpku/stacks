module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.InternalHom

/-!
# Depth bounds for internal Hom stalks

This file gives pointwise depth bounds for the internal Hom of coherent modules on a locally
Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalClosed
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsCoherent]

/-- If a coherent module has stalk depth at least one, then its internal Hom from another
coherent module has stalk depth at least one. -/
theorem moduleDepth_internalHom_stalk_ge_one_of_moduleDepth_stalk_ge_one
    (x : X)
    (h𝒢x : (1 : ℕ∞) ≤
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat 𝒢 x)) :
    (1 : ℕ∞) ≤
      moduleDepth (X.presheaf.stalk x)
        (RingedSpace.stalkModuleCat ((ihom ℱ).obj 𝒢) x) := sorry

/-- If a coherent module has stalk depth at least two, then its internal Hom from another
coherent module has stalk depth at least two. -/
theorem moduleDepth_internalHom_stalk_ge_two_of_moduleDepth_stalk_ge_two
    (x : X)
    (h𝒢x : (2 : ℕ∞) ≤
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat 𝒢 x)) :
    (2 : ℕ∞) ≤
      moduleDepth (X.presheaf.stalk x)
        (RingedSpace.stalkModuleCat ((ihom ℱ).obj 𝒢) x) := sorry

end AlgebraicGeometry.Scheme.Modules
