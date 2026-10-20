module

public import ReasLib.AlgebraicGeometry.BivariantClass.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The canonical morphism over `S` induced by a closed immersion into the underlying
scheme of an over-object is again a closed immersion on underlying schemes. -/
instance instIsClosedImmersionHomMk
    {S : Scheme.{u}} {X : Over S} {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i] :
    IsClosedImmersion
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left := ‹IsClosedImmersion i›

/-- Multiply bivariant classes on two maps to a common target after restricting the
first class to a displayed cartesian intersection. -/
def intersectionMul
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {W X₂ X₂' X : Over S} [LocallyOfFiniteType W.hom]
    [LocallyOfFiniteType X₂.hom] [LocallyOfFiniteType X₂'.hom]
    [LocallyOfFiniteType X.hom]
    (i₂ : X₂ ⟶ X) (i₂' : X₂' ⟶ X) (j₂ : W ⟶ X₂) (j₂' : W ⟶ X₂')
    (iW : W ⟶ X) [LocallyOfFiniteType i₂'.left]
    (square : IsPullback j₂.left j₂'.left i₂.left i₂'.left)
    (intersection : j₂' ≫ i₂' = iW) {a b : ℤ}
    (c : BivariantClass δ i₂ a) (d : BivariantClass δ i₂' b) :
    BivariantClass δ iW (a + b) :=
  intersection ▸ comp δ j₂' i₂' (restrict δ j₂ j₂' i₂' square a c) d

/-- `intersectionMul` is restriction to the cartesian intersection followed by
bivariant composition and transport to the chosen intersection map. -/
theorem intersectionMul_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {W X₂ X₂' X : Over S} [LocallyOfFiniteType W.hom]
    [LocallyOfFiniteType X₂.hom] [LocallyOfFiniteType X₂'.hom]
    [LocallyOfFiniteType X.hom]
    (i₂ : X₂ ⟶ X) (i₂' : X₂' ⟶ X) (j₂ : W ⟶ X₂) (j₂' : W ⟶ X₂')
    (iW : W ⟶ X) [LocallyOfFiniteType i₂'.left]
    (square : IsPullback j₂.left j₂'.left i₂.left i₂'.left)
    (intersection : j₂' ≫ i₂' = iW) {a b : ℤ}
    (c : BivariantClass δ i₂ a) (d : BivariantClass δ i₂' b) :
    intersectionMul δ i₂ i₂' j₂ j₂' iW square intersection c d =
      intersection ▸ comp δ j₂' i₂' (restrict δ j₂ j₂' i₂' square a c) d := rfl

end AlgebraicGeometry.BivariantClass
