module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Quasi-compactness along surjective morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsQuasiCompact

/-- The target of a surjective morphism of algebraic spaces with quasi-compact
source is quasi-compact. -/
theorem of_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Surjective f] [IsQuasiCompact X] : IsQuasiCompact Y :=
  sorry

end IsQuasiCompact

namespace QuasiCompact

/-- If a composite of morphisms of algebraic spaces is quasi-compact and its
first factor is surjective, then its second factor is quasi-compact. -/
theorem of_comp_surjective {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Surjective f] [QuasiCompact (f ≫ q)] :
    QuasiCompact q :=
  sorry

end QuasiCompact

end AlgebraicGeometry.AlgebraicSpace
