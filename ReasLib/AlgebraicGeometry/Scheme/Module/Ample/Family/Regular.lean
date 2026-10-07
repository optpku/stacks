module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Ample families on regular schemes

A quasi-compact regular scheme with affine diagonal admits an ample family of
invertible modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact regular scheme with affine diagonal has an ample family of invertible
modules. -/
theorem exists_ampleFamily_of_compact_regular_affineDiagonal
    (X : Scheme.{u}) [CompactSpace X] [Regular X]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    ∃ (ι : Type u) (L : ι → X.Modules)
      (hL : ∀ i : ι, Scheme.Modules.Invertible (L i)),
        Scheme.Modules.AmpleFamily L := sorry

end AlgebraicGeometry.Scheme
