module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Category

/-!
# Vector bundles and quasicoherent modules

This file records the anti-equivalence between vector bundles over a scheme and
quasicoherent modules on that scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The category of vector bundles over a scheme is anti-equivalent to its category of
quasicoherent modules. -/
theorem vectorBundleOverOpEquivQCoh (S : Scheme.{u}) :
    Nonempty ((vectorBundleCat S)ᵒᵖ ≌ QCoh S) := sorry

end AlgebraicGeometry.Scheme
