module

public import stacks_project.Chap71.Lemma_71_4_6_Fiber
public import stacks_project.Chap76.Lemma_76_27_3_Gorenstein

/-!
# Composition of Gorenstein morphisms of algebraic spaces

Gorensteinness of morphisms of algebraic spaces is stable under composition,
pointwise and globally, when the fibres of both morphisms and of the composite
are locally Noetherian. Under a flatness hypothesis on the first factor it also
cancels, pointwise and on the image of that factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace gorensteinAt

/-- Lemma 76.27.4 (1): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z`
be morphisms of algebraic spaces over `S` whose fibres, and the fibres of
`f ≫ g`, are locally Noetherian. If `f` is Gorenstein at `x` and `g` is
Gorenstein at `Points.map f x`, then `f ≫ g` is Gorenstein at `x`. -/
@[stacks 0E16]
theorem comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] (x : Points X)
    (hf : gorensteinAt f x) (hg : gorensteinAt g (Points.map f x)) :
    gorensteinAt (f ≫ g) x :=
  sorry

end gorensteinAt

namespace Gorenstein

/-- Lemma 76.27.4 (2): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z`
be morphisms of algebraic spaces over `S` whose fibres, and the fibres of
`f ≫ g`, are locally Noetherian. If `f` and `g` are Gorenstein, then
`f ≫ g` is Gorenstein. -/
@[stacks 0E16]
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] [Gorenstein f] [Gorenstein g] :
    Gorenstein (f ≫ g) :=
  sorry

end Gorenstein

namespace gorensteinAt

/-- Lemma 76.27.4 (3): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z`
be morphisms of algebraic spaces over `S` whose fibres, and the fibres of
`f ≫ g`, are locally Noetherian. If `f ≫ g` is Gorenstein at `x` and `f`
is flat at `x`, then `f` is Gorenstein at `x` and `g` is Gorenstein at
`Points.map f x`. -/
@[stacks 0E16]
theorem of_comp_of_flatAt {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] (x : Points X)
    (hfg : gorensteinAt (f ≫ g) x) (hf : FlatAt f x) :
    gorensteinAt f x ∧ gorensteinAt g (Points.map f x) :=
  sorry

end gorensteinAt

namespace Gorenstein

/-- Lemma 76.27.4 (4): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z`
be morphisms of algebraic spaces over `S` whose fibres, and the fibres of
`f ≫ g`, are locally Noetherian. If `f ≫ g` is Gorenstein and `f` is
flat, then `f` is Gorenstein and `g` is Gorenstein at every point of the
image of `Points.map f`. -/
@[stacks 0E16]
theorem of_comp_of_flat {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] [Gorenstein (f ≫ g)] [Flat f] :
    Gorenstein f ∧
      ∀ y : Points Y, y ∈ Set.range (Points.map f) → gorensteinAt g y :=
  sorry

end Gorenstein

end AlgebraicGeometry.AlgebraicSpace
