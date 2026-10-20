module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation

/-!
# Composition of separation axioms for morphisms of algebraic stacks

DM, quasi-DM, separated, and quasi-separated morphisms of algebraic stacks
are stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace DM

/-- The composition of DM morphisms of algebraic stacks is DM. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [DM f] [DM g] :
    DM (f ≫ g) :=
  sorry

end DM

namespace QuasiDM

/-- The composition of quasi-DM morphisms of algebraic stacks is quasi-DM. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiDM f] [QuasiDM g] :
    QuasiDM (f ≫ g) :=
  sorry

end QuasiDM

namespace Separated

/-- The composition of separated morphisms of algebraic stacks is separated. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Separated f] [Separated g] :
    Separated (f ≫ g) :=
  sorry

end Separated

namespace QuasiSeparated

/-- The composition of quasi-separated morphisms of algebraic stacks is
quasi-separated. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSeparated g] :
    QuasiSeparated (f ≫ g) :=
  sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicStack
