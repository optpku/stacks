module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The spectrum of the global sections of a scheme over `k`, equipped with its canonical
structure morphism to `Spec k`. -/
noncomputable def globalSectionsSpec {k : Type u} [Field k] (X : SchemeOverField k) :
    SchemeOverField k :=
  Over.mk (Scheme.Hom.globalSectionsSpecMap X.hom)

/-- The canonical map from a scheme to the spectrum of its global sections respects the
structure morphisms to the base field. -/
theorem toSpecΓ_over {k : Type u} [Field k] (X : SchemeOverField k) :
    X.left.toSpecΓ ≫ (globalSectionsSpec X).hom = X.hom := sorry

/-- The canonical morphism from a scheme over `k` to the spectrum of its global sections. -/
noncomputable def toGlobalSectionsSpec {k : Type u} [Field k] (X : SchemeOverField k) :
    X ⟶ globalSectionsSpec X :=
  Over.homMk X.left.toSpecΓ (toSpecΓ_over X)

/-- The underlying scheme morphism of `toGlobalSectionsSpec` is `Scheme.toSpecΓ`. -/
theorem toGlobalSectionsSpec_left {k : Type u} [Field k] (X : SchemeOverField k) :
    (toGlobalSectionsSpec X).left = X.left.toSpecΓ := sorry

end AlgebraicGeometry.SchemeOverField
