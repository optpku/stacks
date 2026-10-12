/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_9_2_Closed

/-!
# Descent of separation along a universally closed surjection

A surjective universally closed morphism of algebraic spaces sends a
quasi-separated (resp. separated) source to a quasi-separated (resp.
separated) target, both absolutely and relatively over a base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsAbsolutelyQuasiSeparated

/-- Lemma 67.9.8 (1): if `f : X ⟶ Y` is a surjective universally closed morphism of
algebraic spaces over `S` and `X` is quasi-separated, then `Y` is quasi-separated. -/
@[stacks 05Z2]
theorem of_surjective_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Surjective f] [UniversallyClosed f] [IsAbsolutelyQuasiSeparated X] :
    IsAbsolutelyQuasiSeparated Y :=
  sorry

end IsAbsolutelyQuasiSeparated

namespace IsAbsolutelySeparated

/-- Lemma 67.9.8 (2): if `f : X ⟶ Y` is a surjective universally closed morphism of
algebraic spaces over `S` and `X` is separated, then `Y` is separated. -/
@[stacks 05Z2]
theorem of_surjective_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Surjective f] [UniversallyClosed f] [IsAbsolutelySeparated X] :
    IsAbsolutelySeparated Y :=
  sorry

end IsAbsolutelySeparated

namespace QuasiSeparated

/-- Lemma 67.9.8 (3): if `f : X ⟶ Y` and `g : Y ⟶ B` are morphisms of algebraic
spaces over `S`, `f` is surjective and universally closed, and the composite
`f ≫ g` is quasi-separated, then `g` is quasi-separated. -/
@[stacks 05Z2]
theorem of_comp_surjective_universallyClosed {S : Scheme.{u}}
    {X Y B : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ B) [Surjective f]
    [UniversallyClosed f] [QuasiSeparated (f ≫ g)] : QuasiSeparated g :=
  sorry

end QuasiSeparated

namespace Separated

/-- Lemma 67.9.8 (4): if `f : X ⟶ Y` and `g : Y ⟶ B` are morphisms of algebraic
spaces over `S`, `f` is surjective and universally closed, and the composite
`f ≫ g` is separated, then `g` is separated. -/
@[stacks 05Z2]
theorem of_comp_surjective_universallyClosed {S : Scheme.{u}}
    {X Y B : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ B) [Surjective f]
    [UniversallyClosed f] [Separated (f ≫ g)] : Separated g :=
  sorry

end Separated

end AlgebraicGeometry.AlgebraicSpace
