module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Permanence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Permanence
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation

/-!
# Quasi-compact and quasi-separated morphisms from space properties

A morphism of algebraic spaces out of a quasi-compact source into a
quasi-separated target is quasi-compact. A morphism out of an absolutely
quasi-separated source is quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.8.10: quasi-compactness and quasi-separatedness of morphisms from
properties of their source and target. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.QuasiCompact.of_isQuasiCompact :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated Y],
      QuasiCompact f)

#check
  (AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.of_isAbsolutelyQuasiSeparated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsAbsolutelyQuasiSeparated X],
      QuasiSeparated f)

end AlgebraicGeometry.AlgebraicSpace
