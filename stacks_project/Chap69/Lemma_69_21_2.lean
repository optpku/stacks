module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap69.Lemma_69_21_1

/-!
# Lemma 69.21.2

Ampleness of an invertible sheaf on a proper algebraic space over a Noetherian
ring is preserved and reflected by finite surjective pullback.
-/

@[expose]
public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 69.21.2: let `R` be a Noetherian ring, let `f : Y ⟶ X` be a finite
surjective morphism of algebraic spaces proper over `R`, and let `L` be an
invertible `𝒪_X`-module. Then `X` is a scheme and `L` is ample if and only if
`Y` is a scheme and `f^* L` is ample. -/
@[stacks 0GFB]
theorem isSchemeAndAmple_iff_pullback_of_isFinite_surjective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of R))}
    (πX : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πX]
    (πY : Y ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πY]
    (f : Y ⟶ X) [IsFinite f] [Surjective f]
    (L : X.Modules) [isInvertibleObject L] :
    isSchemeAndAmple L ↔ isSchemeAndAmple ((pullback f).obj L) :=
  sorry

/-- If `X` is a scheme and `L` is ample, then `Y` is a scheme and `f^* L` is ample. -/
theorem pullback_isSchemeAndAmple
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of R))}
    (πX : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πX]
    (πY : Y ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πY]
    (f : Y ⟶ X) [IsFinite f] [Surjective f]
    (L : X.Modules) [isInvertibleObject L] :
    isSchemeAndAmple L → isSchemeAndAmple ((pullback f).obj L) :=
  sorry

/-- If `Y` is a scheme and `f^* L` is ample, then `X` is a scheme and `L` is ample. -/
theorem isSchemeAndAmple_of_pullback
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of R))}
    (πX : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πX]
    (πY : Y ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper πY]
    (f : Y ⟶ X) [IsFinite f] [Surjective f]
    (L : X.Modules) [isInvertibleObject L] :
    isSchemeAndAmple ((pullback f).obj L) → isSchemeAndAmple L :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
