module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Descent of flatness for scheme modules

This file records that flat pullback detects relative flatness of quasi-coherent modules,
both at a point and globally along a surjective morphism, and that flatness descends along
fpqc covering families.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules

open Scheme.Hom

variable {S X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ S)
  (𝒢 : Y.Modules) [𝒢.IsQuasicoherent]

/-- Pullback along a morphism flat at a point detects relative flatness of a
quasi-coherent module at the image point. -/
theorem flatOverAt_iff_pullback_flatOverAt_of_flatAt
    (x : X) (hh : flatAt h x) :
    flatOverAt 𝒢 f (h.base x) ↔
      flatOverAt ((Scheme.Modules.pullback h).obj 𝒢) (h ≫ f) x := sorry

/-- Pullback along a flat surjective morphism detects relative flatness of a
quasi-coherent module over the base. -/
theorem flatOver_iff_pullback_flatOver_of_surjective_of_flat
    [Flat h] [Surjective h] :
    flatOver 𝒢 f ↔
      flatOver ((Scheme.Modules.pullback h).obj 𝒢) (h ≫ f) := sorry

namespace IsFlat

/-- A quasi-coherent scheme module is flat if all its pullbacks along an fpqc covering
family are flat. -/
theorem of_fpqcCovering {X : Scheme.{u}} {ι : Type v}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (family : ι → Over X) (hfamily : Scheme.FpqcCovering family)
    (hpullback : ∀ i : ι, ((Scheme.Modules.pullback (family i).hom).obj ℱ).IsFlat) :
    ℱ.IsFlat := sorry

end IsFlat

end AlgebraicGeometry.Scheme.Modules
