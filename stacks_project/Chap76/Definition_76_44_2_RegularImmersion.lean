module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap76.Lemma_76_44_1_EtaleLocalOnTarget

/-!
# Regular immersions of algebraic spaces

This module retains the source-facing compatibility instances for the
immersion interface of regular immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A Koszul-regular immersion of algebraic spaces is an immersion. -/
instance IsImmersion.ofIsKoszulRegularImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {i : X ⟶ Y} [IsKoszulRegularImmersion i] :
    IsImmersion i :=
  ⟨IsKoszulRegularImmersion.immersionPresheaf i⟩

/-- An `H₁`-regular immersion of algebraic spaces is an immersion. -/
instance IsImmersion.ofIsH1RegularImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {i : X ⟶ Y} [IsH1RegularImmersion i] :
    IsImmersion i :=
  ⟨IsH1RegularImmersion.immersionPresheaf i⟩

/-- A quasi-regular immersion of algebraic spaces is an immersion. -/
instance IsImmersion.ofIsQuasiRegularImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {i : X ⟶ Y} [IsQuasiRegularImmersion i] :
    IsImmersion i :=
  ⟨IsQuasiRegularImmersion.immersionPresheaf i⟩

end AlgebraicGeometry.AlgebraicSpace
