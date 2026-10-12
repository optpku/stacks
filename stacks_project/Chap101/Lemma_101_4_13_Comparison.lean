/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_4_2_Separation
public import stacks_project.Chap101.Definition_101_8_1_Noetherian

/-!
# Absolute versus relative separation axioms

For an algebraic stack over a scheme `S`, being DM or quasi-DM is equivalent
to the corresponding property over `S`. Absolute separatedness and
quasi-separatedness imply the relative versions. Morphisms out of a stack
that is DM or quasi-DM over `S` inherit the same morphism axiom; the
separated and quasi-separated cases additionally require the object
diagonal of the target to be separated or quasi-separated as a
representable morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace IsDM

/-- An algebraic stack that is DM is DM over its base scheme. -/
theorem spec_over {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsDM X] : IsDMOver X :=
  sorry

/-- Being DM over the base scheme witnesses that an algebraic stack is DM. -/
theorem of_over {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : IsDMOver X) : IsDM X :=
  sorry

/-- An algebraic stack over `S` is DM if and only if it is DM over `S`. -/
theorem iff_over {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsDM X ↔ IsDMOver X :=
  sorry

end IsDM

namespace IsQuasiDM

/-- An algebraic stack that is quasi-DM is quasi-DM over its base scheme. -/
theorem spec_over {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsQuasiDM X] : IsQuasiDMOver X :=
  sorry

/-- Being quasi-DM over the base scheme witnesses that an algebraic stack is
quasi-DM. -/
theorem of_over {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : IsQuasiDMOver X) : IsQuasiDM X :=
  sorry

/-- An algebraic stack over `S` is quasi-DM if and only if it is quasi-DM over
`S`. -/
theorem iff_over {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsQuasiDM X ↔ IsQuasiDMOver X :=
  sorry

end IsQuasiDM

namespace IsSeparatedOver

/-- A separated algebraic stack is separated over its base scheme. -/
instance of_isSeparated {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsSeparated X] : IsSeparatedOver X :=
  sorry

end IsSeparatedOver

namespace IsQuasiSeparatedOver

/-- A quasi-separated algebraic stack is quasi-separated over its base
scheme. -/
instance of_isQuasiSeparated {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiSeparated X] : IsQuasiSeparatedOver X :=
  sorry

end IsQuasiSeparatedOver

namespace DM

/-- A morphism of algebraic stacks over `S` out of a stack that is DM over `S`
is DM. -/
instance of_isDMOver {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsDMOver X] :
    DM f :=
  sorry

end DM

namespace QuasiDM

/-- A morphism of algebraic stacks over `S` out of a stack that is quasi-DM
over `S` is quasi-DM. -/
instance of_isQuasiDMOver {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsQuasiDMOver X] :
    QuasiDM f :=
  sorry

end QuasiDM

namespace Separated

/-- If `X` is separated over `S` and the object diagonal of `Y` is separated
as a representable morphism of algebraic spaces, then a morphism `f : X ⟶ Y`
of algebraic stacks over `S` is separated. -/
theorem of_isSeparatedOver {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsSeparatedOver X]
    (h_separated :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (diagonal.{u + 1, u, u + 1} Y)) :
    Separated f :=
  sorry

end Separated

namespace QuasiSeparated

/-- If `X` is quasi-separated over `S` and the object diagonal of `Y` is
quasi-separated as a representable morphism of algebraic spaces, then a
morphism `f : X ⟶ Y` of algebraic stacks over `S` is quasi-separated. -/
theorem of_isQuasiSeparatedOver {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiSeparatedOver X]
    (h_quasiSeparated :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (diagonal.{u + 1, u, u + 1} Y)) :
    QuasiSeparated f :=
  sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicStack
