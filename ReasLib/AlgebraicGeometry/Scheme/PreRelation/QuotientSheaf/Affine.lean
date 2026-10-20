module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The fppf quotient sheaf of an étale equivalence relation on an affine scheme over
a base scheme has representable diagonal. -/
theorem quotientSheaf_representableDiagonal_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    uliftYoneda.{u + 1}.relativelyRepresentable
      (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj) := sorry

/-- The canonical map to the fppf quotient of an étale equivalence relation on an
affine scheme is representable, étale, and surjective. -/
theorem quotientMap_etale_surjective_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    (MorphismProperty.over (@Etale ⊓ @Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map to the fppf quotient of an étale equivalence relation on an
affine scheme is relatively representable with respect to `uliftYoneda`. -/
theorem quotientMap_relativelyRepresentable_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    uliftYoneda.{u + 1}.relativelyRepresentable
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map to the fppf quotient of an étale equivalence relation on an
affine scheme is representable and étale with respect to `uliftYoneda`. -/
theorem quotientMap_etale_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map to the fppf quotient of an étale equivalence relation on an
affine scheme is representable and has surjective represented pullbacks. -/
theorem quotientMap_surjective_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map to the fppf quotient of an étale equivalence relation on an
affine scheme is étale-locally surjective. -/
theorem quotientMap_locallySurjective_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The fppf quotient sheaf of an étale equivalence relation on an affine scheme
over `S` has representable diagonal, and its canonical atlas is representable étale
and étale-locally surjective. -/
theorem quotientSheaf_spec_of_isAffine {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] [IsAffine U.left] :
    uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj) ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

end AlgebraicGeometry.Scheme.PreRelation
