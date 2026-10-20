module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Separation properties inherited from the source

A morphism of algebraic spaces whose source is separated, locally separated, or
quasi-separated over the base has the corresponding morphism property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Separated

/-- A morphism of algebraic spaces out of a relatively separated source is separated. -/
instance (priority := 900) of_isSeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsSeparated X] : Separated f := sorry

end Separated

namespace LocallySeparated

/-- A morphism of algebraic spaces out of a relatively locally separated source is locally
separated. -/
instance (priority := 900) of_isLocallySeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallySeparated X] : LocallySeparated f := sorry

end LocallySeparated

namespace QuasiSeparated

/-- A morphism of algebraic spaces out of a relatively quasi-separated source is
quasi-separated. -/
instance (priority := 900) of_isQuasiSeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiSeparated X] : QuasiSeparated f := sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
