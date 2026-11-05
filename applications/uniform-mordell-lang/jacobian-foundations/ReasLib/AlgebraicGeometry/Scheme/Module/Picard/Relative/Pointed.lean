module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Graph.Cartier
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Quotient

/-!
# Pointed Picard maps before representability

For a separated smooth relative curve `X → S`, a `T`-point gives the class of
its graph divisor. A section `P : S → X` normalizes this to `O(Γₓ - Γₚ)`.
The raw, relative-quotient and fppf maps are constructed on functors of points.
They require neither properness nor a field, Hilbert scheme or Picard scheme.

The represented-map interface is in `Pointed.Represented`. Landing in a chosen
subfunctor is a separate hypothesis there: degree-zero membership and geometric
properties belong to the relevant curve theory, not to this construction.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory

noncomputable section
universe u

namespace AlgebraicGeometry.RelativePicard

variable {S : Scheme.{u}} (X : Over S)
variable [IsSeparated X.hom] [SmoothOfRelativeDimension 1 X.hom]

/-- The raw Picard class of the graph of a point. -/
noncomputable def sectionClass {T : Over S} (x : T ⟶ X) :
    (presheaf X).obj (op T) :=
  Scheme.Modules.picardClass (SchemeOver.graphLineBundle x)

/-- Graph line-bundle classes commute with pullback of test schemes. -/
theorem sectionClass_naturality {T T' : Over S} (x : T ⟶ X) (f : T' ⟶ T) :
    (presheaf X).map f.op (sectionClass X x) = sectionClass X (f ≫ x) := by
  sorry

/-- The graph-divisor class as a natural transformation on points. -/
noncomputable def sectionMap : uliftYoneda.{u + 1}.obj X ⟶ presheaf X where
  app T := TypeCat.ofHom (fun x ↦ sectionClass X x.down)
  naturality := by
    intro T T' f
    ext x
    exact (sectionClass_naturality X x.down f.unop).symm

/-- The graph-class transformation evaluates to the class of the actual graph. -/
@[simp]
theorem sectionMap_app {T : Over S} (x : T ⟶ X) :
    (sectionMap X).app (op T) (ULift.up x) = sectionClass X x := rfl

/-- The normalized class `O(Γₓ - Γₚ)`; subtraction is tensoring with the dual. -/
noncomputable def pointedSectionClass (P : 𝟙_ (Over S) ⟶ X)
    {T : Over S} (x : T ⟶ X) : (presheaf X).obj (op T) :=
  sectionClass X x - sectionClass X (CartesianMonoidalCategory.toUnit T ≫ P)

/-- The normalized graph class is natural in the test scheme. -/
theorem pointedSectionClass_naturality (P : 𝟙_ (Over S) ⟶ X)
    {T T' : Over S} (x : T ⟶ X) (f : T' ⟶ T) :
    (presheaf X).map f.op (pointedSectionClass X P x) =
      pointedSectionClass X P (f ≫ x) := by
  sorry

/-- The pointed Abel class as a map into raw Picard classes. -/
noncomputable def pointedSectionMap (P : 𝟙_ (Over S) ⟶ X) :
    uliftYoneda.{u + 1}.obj X ⟶ presheaf X where
  app T := TypeCat.ofHom (fun x ↦ pointedSectionClass X P x.down)
  naturality := by
    intro T T' f
    ext x
    exact (pointedSectionClass_naturality X P x.down f.unop).symm

/-- Evaluation of the pointed transformation is the normalized graph class. -/
@[simp]
theorem pointedSectionMap_app (P : 𝟙_ (Over S) ⟶ X) {T : Over S} (x : T ⟶ X) :
    (pointedSectionMap X P).app (op T) (ULift.up x) = pointedSectionClass X P x := rfl

/-- Normalization sends the chosen section to the trivial line-bundle class. -/
@[simp]
theorem pointedSectionClass_basePoint (P : 𝟙_ (Over S) ⟶ X) :
    pointedSectionClass X P P = 0 := by
  sorry

/-- The pointed map into relative quotient classes. -/
noncomputable def pointedQuotientMap (P : 𝟙_ (Over S) ⟶ X) :
    uliftYoneda.{u + 1}.obj X ⟶ quotientPresheaf X ⋙ forget AddCommGrpCat :=
  pointedSectionMap X P ≫
    Functor.whiskerRight (toQuotientPresheaf X) (forget AddCommGrpCat)

/-- The pointed map into the relative Picard fppf sheaf. -/
noncomputable def pointedFppfMap (P : 𝟙_ (Over S) ⟶ X) :
    uliftYoneda.{u + 1}.obj X ⟶ (functor X).obj :=
  pointedSectionMap X P ≫
    (Scheme.fppfTopology.over S).toSheafify (presheaf X)

end AlgebraicGeometry.RelativePicard
