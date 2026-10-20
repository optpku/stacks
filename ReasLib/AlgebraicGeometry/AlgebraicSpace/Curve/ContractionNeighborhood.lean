module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Family
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.OverMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Hom

/-!
# Spreading fibrewise contraction of a morphism of curve families

If a morphism of families of curves over a scheme induces an isomorphism on
structure sheaves and vanishing of `R¹` on a fibre, then the same conclusions
hold after replacing the base by an open neighbourhood of that point, and they
remain true after every further base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Let `f : X ⟶ S` and `g : Y ⟶ S` be families of curves, and let `c : X ⟶ Y`
be a morphism over `S`. If `Modules.unitToPushforwardObjUnit (fiberMap c hc s)`
is an isomorphism and `higherDirectImageOne (fiberMap c hc s)` is zero, then
there is an open neighbourhood `U` of `s` such that
`Modules.unitToPushforwardObjUnit (overMap c hc (φ ≫ openι U))` is an
isomorphism and `higherDirectImageOne (overMap c hc (φ ≫ openι U))` vanishes,
for every morphism `φ` of algebraic spaces into `ofOver (Over.mk U.ι)`. -/
theorem exists_open_of_fiber {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) (g : Y ⟶ ofOver (Over.mk (𝟙 S)))
    [IsFamily f] [IsFamily g] (c : X ⟶ Y) (hc : c ≫ g = f) (s : S)
    (h_unit : IsIso (Modules.unitToPushforwardObjUnit (fiberMap c hc s)))
    (h_R1 : IsZero (higherDirectImageOne (fiberMap c hc s))) :
    ∃ U : S.Opens, s ∈ U ∧
      ∀ {Z : AlgebraicSpace S} (φ : Z ⟶ ofOver (Over.mk U.ι)),
        IsIso (Modules.unitToPushforwardObjUnit (overMap c hc (φ ≫ openι U))) ∧
          IsZero (higherDirectImageOne (overMap c hc (φ ≫ openι U))) :=
  sorry

/-- The open neighbourhood of `s` supplied by `exists_open_of_fiber` contains
`s`, and after every base change of that open the structure-sheaf unit is an
isomorphism and `R¹` of the structure sheaf vanishes. -/
theorem exists_open_of_fiber_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) (g : Y ⟶ ofOver (Over.mk (𝟙 S)))
    [IsFamily f] [IsFamily g] (c : X ⟶ Y) (hc : c ≫ g = f) (s : S)
    (h_unit : IsIso (Modules.unitToPushforwardObjUnit (fiberMap c hc s)))
    (h_R1 : IsZero (higherDirectImageOne (fiberMap c hc s))) :
    ∃ U : S.Opens,
      s ∈ U ∧
        (∀ {Z : AlgebraicSpace S} (φ : Z ⟶ ofOver (Over.mk U.ι)),
          IsIso (Modules.unitToPushforwardObjUnit (overMap c hc (φ ≫ openι U)))) ∧
        ∀ {Z : AlgebraicSpace S} (φ : Z ⟶ ofOver (Over.mk U.ι)),
          IsZero (higherDirectImageOne (overMap c hc (φ ≫ openι U))) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
