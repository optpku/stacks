module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap76.Lemma_76_15_8_Comparison

/-!
# Base change of universal first-order thickenings of algebraic spaces

Universality to first order is preserved by cartesian base change. The fibre
product `X ×_Y W ⊂ X ×_Y W'` of a universal first-order thickening of `W`
over `Y` is a universal first-order thickening of `X ×_Y W` over `X`, and the
canonical Lemma 76.15.8 comparison of conormal sheaves is an epimorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

/-- Universality to first order is preserved by a cartesian base change of both the
closed and ambient algebraic spaces of a thickening. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z W Z' W' : AlgebraicSpace S}
    (g : X ⟶ Y) (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) (f' : Z' ⟶ W') (closedSq : CommSq f iZ iW f')
    (leftSq : IsPullback f (iZ ≫ fZ) (iW ≫ fW) g)
    (rightSq : IsPullback f' fZ fW g) [IsUniversalFirstOrder iW fW] :
    IsUniversalFirstOrder iZ fZ :=
  sorry

/-- The closed immersion `X ×_Y W ⟶ X ×_Y W'` induced by a first-order thickening
`W ⊂ W'` over `Y`. -/
noncomputable def pullbackHom {S : Scheme.{u}} {X Y W W' : AlgebraicSpace S}
    (g : X ⟶ Y) (iW : W ⟶ W') (fW : W' ⟶ Y) :
    pullback g (iW ≫ fW) ⟶ pullback g fW :=
  pullback.map g (iW ≫ fW) g fW (𝟙 X) iW (𝟙 Y)
    ((Category.comp_id g).trans (Category.id_comp g).symm)
    (Category.comp_id (iW ≫ fW))

/-- The closed-to-base composite of `pullbackHom` is the projection of
`X ×_Y W` to `X`. -/
theorem pullbackHom_fst {S : Scheme.{u}} {X Y W W' : AlgebraicSpace S}
    (g : X ⟶ Y) (iW : W ⟶ W') (fW : W' ⟶ Y) :
    pullbackHom g iW fW ≫ pullback.fst g fW = pullback.fst g (iW ≫ fW) :=
  sorry

/-- The ambient comparison of `pullbackHom` is the composite of the projection of
`X ×_Y W` to `W` with `W ⊂ W'`. -/
theorem pullbackHom_snd {S : Scheme.{u}} {X Y W W' : AlgebraicSpace S}
    (g : X ⟶ Y) (iW : W ⟶ W') (fW : W' ⟶ Y) :
    pullbackHom g iW fW ≫ pullback.snd g fW = pullback.snd g (iW ≫ fW) ≫ iW :=
  sorry

/-- The chosen fibre product `X ×_Y W ⊂ X ×_Y W'` of a universal first-order
thickening of `W` over `Y` is a universal first-order thickening of
`X ×_Y W` over `X`. -/
instance pullback_isUniversal {S : Scheme.{u}} {X Y W W' : AlgebraicSpace S}
    (g : X ⟶ Y) (iW : W ⟶ W') (fW : W' ⟶ Y) [IsUniversalFirstOrder iW fW] :
    IsUniversalFirstOrder (pullbackHom g iW fW) (pullback.fst g fW) :=
  sorry

/-- In a cartesian cube of thickenings, the Lemma 76.15.8 comparison of ambient
spaces is the given ambient projection. -/
theorem comparison_eq_of_isPullback {S : Scheme.{u}}
    {X Y Z W Z' W' : AlgebraicSpace S}
    (g : X ⟶ Y) (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) (f' : Z' ⟶ W')
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)]
    (closedSq : CommSq f iZ iW f')
    (leftSq : IsPullback f (iZ ≫ fZ) (iW ≫ fW) g)
    (rightSq : IsPullback f' fZ fW g) :
    comparison iZ fZ iW fW f g ⟨leftSq.w⟩ = f' :=
  sorry

/-- For a cartesian base change of a universal first-order thickening along a
formally unramified morphism, the canonical Lemma 76.15.8 comparison of
conormal sheaves is an epimorphism. -/
theorem conormalMap_epi {S : Scheme.{u}} {X Y Z W Z' W' : AlgebraicSpace S}
    (g : X ⟶ Y) (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) (f' : Z' ⟶ W')
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)]
    (leftSq : IsPullback f (iZ ≫ fZ) (iW ≫ fW) g)
    (thickeningSq : IsPullback f iZ iW f')
    (rightSq : IsPullback f' fZ fW g) :
    Epi (conormalMap iZ fZ iW fW f g ⟨leftSq.w⟩) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

