module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.UnderlyingHomotopyEquivalence

/-!
# Detecting simplicial homotopy equivalences through additive functors

An additive homology-preserving functor that reflects isomorphisms transports the underlying
simplicial-set homotopy-equivalence criterion from additive groups to its source category.  The
result is expressed as an inclusion of morphism properties, so it composes with further inverse
images without rebuilding pointwise theorems.
-/

@[expose] public section

open CategoryTheory HomologicalComplex
open AlgebraicTopology

universe u v w

namespace CategoryTheory.SimplicialObject

namespace AddCommGrp.underlying.homotopyEquivalences

namespace alternatingFace

/-- Pulling underlying homotopy equivalences back along an additive homology-preserving functor
that reflects isomorphisms gives alternating-face quasi-isomorphisms. -/
@[stacks 08P2 "underlying homotopy equivalences detected by an additive functor"]
theorem inverseImage_le_quasiIso
    {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
    (F : A ⥤ AddCommGrpCat.{w}) [F.Additive] [F.PreservesHomology]
    [F.ReflectsIsomorphisms] :
    AddCommGrp.underlying.homotopyEquivalences.inverseImage
        ((Functor.whiskeringRight SimplexCategoryᵒᵖ A AddCommGrpCat.{w}).obj F) ≤
      (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).inverseImage
        (alternatingFaceMapComplex A) := sorry

end alternatingFace

namespace normalizedMoore

/-- Pulling underlying homotopy equivalences back along an additive homology-preserving functor
that reflects isomorphisms gives normalized-Moore quasi-isomorphisms. -/
@[stacks 08P2 "underlying homotopy equivalences and normalized Moore complexes"]
theorem inverseImage_le_quasiIso
    {A : Type u} [Category.{v} A] [Abelian A]
    (F : A ⥤ AddCommGrpCat.{w}) [F.Additive] [F.PreservesHomology]
    [F.ReflectsIsomorphisms] :
    AddCommGrp.underlying.homotopyEquivalences.inverseImage
        ((Functor.whiskeringRight SimplexCategoryᵒᵖ A AddCommGrpCat.{w}).obj F) ≤
      (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).inverseImage
        (normalizedMooreComplex A) := sorry

end normalizedMoore

end AddCommGrp.underlying.homotopyEquivalences

end CategoryTheory.SimplicialObject
