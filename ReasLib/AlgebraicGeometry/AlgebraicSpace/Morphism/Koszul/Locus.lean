module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Koszul.Locus

/-!
# Koszul loci of morphisms of algebraic spaces

The points where a morphism is Koszul form a canonical open subspace.
For morphisms between algebraic spaces flat and locally of finite presentation
over a common base, this open subspace commutes with arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The set of points where a morphism of algebraic spaces is Koszul is open. -/
theorem isOpen_koszulAt_locus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsOpen {x | KoszulAt f x} :=
  sorry

/-- The open subspace consisting of the points where the morphism is Koszul. -/
def koszulLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : OpenSubspace X :=
  OpenSubspace.fromOpens ⟨{x | KoszulAt f x}, isOpen_koszulAt_locus f⟩

/-- The point set of the Koszul locus is the set of Koszul points. -/
theorem koszulLocus_pointsSet_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : (koszulLocus f).pointsSet = {x | KoszulAt f x} :=
  OpenSubspace.fromOpens_pointsSet _

/-- A point belongs to the Koszul locus exactly when the morphism is Koszul there. -/
theorem mem_koszulLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    x ∈ (koszulLocus f).pointsSet ↔ KoszulAt f x := by
  rw [koszulLocus_pointsSet_eq]
  rfl

/-- For a morphism over a common base with flat, locally finitely presented
structure maps, the Koszul locus consists exactly of its Koszul points. -/
theorem koszulLocus_pointsSet_eq_of_over {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (h_over : f ≫ q = p) [Flat p] [LocallyOfFinitePresentation p]
    [Flat q] [LocallyOfFinitePresentation q] :
    (koszulLocus f).pointsSet = {x | KoszulAt f x} :=
  sorry

/-- Under arbitrary base change, the Koszul locus of a morphism between spaces
flat and locally of finite presentation over the base is the inverse image
of its original Koszul locus. -/
theorem koszulLocus_pointsSet_eq_preimage_of_baseChange {S : Scheme.{u}}
    {X Y Z X' Y' Z' : AlgebraicSpace S} (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (f' : X' ⟶ Y') (p' : X' ⟶ Z') (q' : Y' ⟶ Z') (gX : X' ⟶ X) (gY : Y' ⟶ Y)
    (g : Z' ⟶ Z) (h_over : f ≫ q = p) (h_over' : f' ≫ q' = p')
    (sq : CommSq f' gX gY f) (hX : IsPullback gX p' p g)
    (hY : IsPullback gY q' q g) [Flat p] [LocallyOfFinitePresentation p]
    [Flat q] [LocallyOfFinitePresentation q] :
    (koszulLocus f').pointsSet = Points.map gX ⁻¹' (koszulLocus f).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
