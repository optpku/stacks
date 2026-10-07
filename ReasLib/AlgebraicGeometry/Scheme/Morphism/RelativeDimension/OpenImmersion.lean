module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.QuasiFinite

/-!
# Relative dimension of open immersions

Open immersions have relative dimension zero.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An open immersion has relative dimension zero. -/
theorem relativeDimension_zero_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : RelativeDimension f 0 := sorry

end AlgebraicGeometry.Scheme.Hom
