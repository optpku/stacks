module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap76.«76_15_0_1_Universal»
public import stacks_project.Chap76.Lemma_76_14_4_FormallyUnramified
public import stacks_project.Chap76.Lemma_76_5_3_Map

/-!
# Comparison of universal first-order thickenings of algebraic spaces

A commutative square of formally unramified morphisms of algebraic spaces
induces a canonical map of universal first-order thickenings, and therefore the
Lemma 76.5.3 morphism of conormal sheaves of the closed immersions `Z ⊂ Z'` and
`W ⊂ W'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

/-- The unique ambient extension of a solid map from a first-order thickening to a
universal first-order thickening over the same base. -/
noncomputable def lift {S : Scheme.{u}} {Y W W' T T' : AlgebraicSpace S}
    (i : W ⟶ W') (fW : W' ⟶ Y) [IsUniversalFirstOrder i fW]
    (j : T ⟶ T') (b : T' ⟶ Y) [IsFirstOrderThickening j]
    (a : T ⟶ W) (h_solid : a ≫ i ≫ fW = j ≫ b) : T' ⟶ W' :=
  (existsUniqueLift j b a h_solid).choose

/-- The canonical ambient map of universal first-order thickenings associated to a
commutative square of formally unramified morphisms. -/
noncomputable def comparison {S : Scheme.{u}}
    {X Y Z W Z' W' : AlgebraicSpace S}
    (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) (g : X ⟶ Y)
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)]
    (sq : CommSq f (iZ ≫ fZ) (iW ≫ fW) g) : Z' ⟶ W' :=
  lift iW fW iZ (fZ ≫ g) f (sq.w.trans (Category.assoc iZ fZ g))

/-- The closed-subspace square of the canonical comparison of universal
first-order thickenings. -/
noncomputable def comparison_comp {S : Scheme.{u}}
    {X Y Z W Z' W' : AlgebraicSpace S}
    (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) (g : X ⟶ Y)
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)]
    (sq : CommSq f (iZ ≫ fZ) (iW ≫ fW) g) :
    f ≫ iW = iZ ≫ comparison iZ fZ iW fW f g sq :=
  (existsUniqueLift (i := iW) (f := fW) iZ (fZ ≫ g) f
      (sq.w.trans (Category.assoc iZ fZ g))).choose_spec.left.left

/-- The canonical comparison of universal first-order thickenings is a morphism
over `Y`. -/
noncomputable def comparison_over {S : Scheme.{u}}
    {X Y Z W Z' W' : AlgebraicSpace S}
    (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) (g : X ⟶ Y)
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)]
    (sq : CommSq f (iZ ≫ fZ) (iW ≫ fW) g) :
    comparison iZ fZ iW fW f g sq ≫ fW = fZ ≫ g :=
  (existsUniqueLift (i := iW) (f := fW) iZ (fZ ≫ g) f
      (sq.w.trans (Category.assoc iZ fZ g))).choose_spec.left.right

/-- The canonical comparison is the unique morphism of thickenings over `Y`
extending the given map on closed subspaces. -/
theorem comparison_unique {S : Scheme.{u}}
    {X Y Z W Z' W' : AlgebraicSpace S}
    (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) (g : X ⟶ Y)
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)]
    (sq : CommSq f (iZ ≫ fZ) (iW ≫ fW) g)
    (k : Z' ⟶ W') (h_closed : f ≫ iW = iZ ≫ k)
    (h_over : k ≫ fW = fZ ≫ g) :
    k = comparison iZ fZ iW fW f g sq :=
  sorry

/-- The morphism of conormal sheaves induced by the canonical comparison of
universal first-order thickenings. -/
noncomputable def conormalMap {S : Scheme.{u}}
    {X Y Z W Z' W' : AlgebraicSpace S}
    (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) (g : X ⟶ Y)
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)]
    (sq : CommSq f (iZ ≫ fZ) (iW ≫ fW) g) :
    (Modules.pullback f).obj (Hom.conormalSheaf iW) ⟶ Hom.conormalSheaf iZ :=
  Hom.Conormal.map ⟨comparison_comp iZ fZ iW fW f g sq⟩

/-- The induced conormal morphism is the comparison of Lemma 76.5.3 applied to the
thickening square. -/
theorem conormalMap_eq {S : Scheme.{u}}
    {X Y Z W Z' W' : AlgebraicSpace S}
    (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) (g : X ⟶ Y)
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)]
    (sq : CommSq f (iZ ≫ fZ) (iW ≫ fW) g) :
    conormalMap iZ fZ iW fW f g sq =
      Hom.Conormal.map ⟨comparison_comp iZ fZ iW fW f g sq⟩ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
