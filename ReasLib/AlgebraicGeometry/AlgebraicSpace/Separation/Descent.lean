/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed

/-!
# Descent of separation along a universally closed surjection

Absolute and relative quasi-separatedness and separatedness descend along
surjective universally closed morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsAbsolutelyQuasiSeparated

/-- The target of a surjective universally closed morphism from an absolutely
quasi-separated algebraic space is absolutely quasi-separated. -/
theorem of_surjective_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Surjective f] [UniversallyClosed f] [IsAbsolutelyQuasiSeparated X] :
    IsAbsolutelyQuasiSeparated Y :=
  sorry

end IsAbsolutelyQuasiSeparated

namespace IsAbsolutelySeparated

/-- The target of a surjective universally closed morphism from an absolutely
separated algebraic space is absolutely separated. -/
theorem of_surjective_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Surjective f] [UniversallyClosed f] [IsAbsolutelySeparated X] :
    IsAbsolutelySeparated Y :=
  sorry

end IsAbsolutelySeparated

namespace QuasiSeparated

/-- A morphism of algebraic spaces is quasi-separated if its composite with a
surjective universally closed morphism is quasi-separated. -/
theorem of_comp_surjective_universallyClosed {S : Scheme.{u}}
    {X Y B : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ B) [Surjective f]
    [UniversallyClosed f] [QuasiSeparated (f ≫ g)] : QuasiSeparated g :=
  sorry

end QuasiSeparated

namespace Separated

/-- A morphism of algebraic spaces is separated if its composite with a
surjective universally closed morphism is separated. -/
theorem of_comp_surjective_universallyClosed {S : Scheme.{u}}
    {X Y B : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ B) [Surjective f]
    [UniversallyClosed f] [Separated (f ≫ g)] : Separated g :=
  sorry

end Separated

end AlgebraicGeometry.AlgebraicSpace
