module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Permanence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Permanence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap67.Lemma_67_8_10_Instances
public import stacks_project.Chap66.Definition_66_3_1_Separation

/-!
# Fibre products of quasi-compact quasi-separated algebraic spaces

The vertex of a pullback of algebraic spaces inherits quasi-compactness from the
two factors when the target is quasi-separated, and inherits absolute
quasi-separatedness from the two factors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.8.10: quasi-compactness and absolute quasi-separatedness of fibre
products of algebraic spaces. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact.of_isPullback :
    ∀ {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S} {f : X ⟶ Y} {g : Z ⟶ Y}
      {pZ : P ⟶ Z} {pX : P ⟶ X}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated Y] [IsQuasiCompact Z],
      IsPullback pZ pX g f → IsQuasiCompact P)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated.of_isPullback :
    ∀ {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S} {f : X ⟶ Y} {g : Z ⟶ Y}
      {pZ : P ⟶ Z} {pX : P ⟶ X}
      [IsAbsolutelyQuasiSeparated X] [IsAbsolutelyQuasiSeparated Z],
      IsPullback pZ pX g f → IsAbsolutelyQuasiSeparated P)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact.instPullback :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated Y] [IsQuasiCompact Z]
      [HasPullback f g],
      IsQuasiCompact (pullback f g))

#check
  (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated.instPullback :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
      [IsAbsolutelyQuasiSeparated X] [IsAbsolutelyQuasiSeparated Z]
      [HasPullback f g],
      IsAbsolutelyQuasiSeparated (pullback f g))

end AlgebraicGeometry.AlgebraicSpace
