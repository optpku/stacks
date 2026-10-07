module

public import stacks_project.Chap76.Lemma_76_26_3_CohenMacaulay

/-!
# Composition of Cohen--Macaulay morphisms of algebraic spaces

Cohen--Macaulayness of morphisms of algebraic spaces is stable under
composition, pointwise and globally, when the fibres of both morphisms and
of the composite are locally Noetherian. Under a flatness hypothesis on the
first factor it also cancels, pointwise and on the image of that factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace CohenMacaulayAt

/-- Lemma 76.26.4 (1): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z`
be morphisms of algebraic spaces over `S` whose fibres, and the fibres of
`f ≫ g`, are locally Noetherian. If `f` is Cohen--Macaulay at `x` and `g` is
Cohen--Macaulay at `Points.map f x`, then `f ≫ g` is Cohen--Macaulay at `x`. -/
@[stacks 0E0X]
theorem comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] (x : Points X)
    (hf : CohenMacaulayAt f x) (hg : CohenMacaulayAt g (Points.map f x)) :
    CohenMacaulayAt (f ≫ g) x :=
  sorry

end CohenMacaulayAt

namespace CohenMacaulay

/-- Lemma 76.26.4 (2): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z`
be morphisms of algebraic spaces over `S` whose fibres, and the fibres of
`f ≫ g`, are locally Noetherian. If `f` and `g` are Cohen--Macaulay, then
`f ≫ g` is Cohen--Macaulay. -/
@[stacks 0E0X]
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] [CohenMacaulay f] [CohenMacaulay g] :
    CohenMacaulay (f ≫ g) :=
  sorry

end CohenMacaulay

namespace CohenMacaulayAt

/-- Lemma 76.26.4 (3): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z`
be morphisms of algebraic spaces over `S` whose fibres, and the fibres of
`f ≫ g`, are locally Noetherian. If `f ≫ g` is Cohen--Macaulay at `x` and `f`
is flat at `x`, then `f` is Cohen--Macaulay at `x` and `g` is Cohen--Macaulay
at `Points.map f x`. -/
@[stacks 0E0X]
theorem of_comp_of_flatAt {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] (x : Points X)
    (hfg : CohenMacaulayAt (f ≫ g) x) (hf : FlatAt f x) :
    CohenMacaulayAt f x ∧ CohenMacaulayAt g (Points.map f x) :=
  sorry

end CohenMacaulayAt

namespace CohenMacaulay

/-- Lemma 76.26.4 (4): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z`
be morphisms of algebraic spaces over `S` whose fibres, and the fibres of
`f ≫ g`, are locally Noetherian. If `f ≫ g` is Cohen--Macaulay and `f` is
flat, then `f` is Cohen--Macaulay and `g` is Cohen--Macaulay at every point
of the image of `Points.map f`. -/
@[stacks 0E0X]
theorem of_comp_of_flat {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] [CohenMacaulay (f ≫ g)] [Flat f] :
    CohenMacaulay f ∧
      ∀ y : Points Y, y ∈ Set.range (Points.map f) → CohenMacaulayAt g y :=
  sorry

end CohenMacaulay

end AlgebraicGeometry.AlgebraicSpace
