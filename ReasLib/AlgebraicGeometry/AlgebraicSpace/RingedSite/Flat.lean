module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Flat morphisms of algebraic spaces via the small étale site

A morphism of algebraic spaces is flat if and only if its canonical inverse-image
structure-sheaf map on the small étale site is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces over a scheme is flat if and only if its
canonical inverse-image structure-sheaf map on the small étale site is flat. -/
theorem flat_iff_isFlatHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    Flat f ↔ IsFlatHom.{u + 1, u, u} (commInverseImageStructureSheafMap f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
