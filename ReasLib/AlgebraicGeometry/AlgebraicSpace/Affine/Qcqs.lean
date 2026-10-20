module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Quasi-compactness and quasi-separatedness of affine morphisms

Affine morphisms of algebraic spaces are quasi-compact and quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Affine

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- An affine morphism of algebraic spaces is quasi-compact. -/
instance quasiCompact (f : X ⟶ Y) [Affine f] : QuasiCompact f :=
  sorry

/-- An affine morphism of algebraic spaces is quasi-separated. -/
instance quasiSeparated (f : X ⟶ Y) [Affine f] : QuasiSeparated f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Affine
