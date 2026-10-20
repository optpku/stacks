/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.KernelPair

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The canonical map to the fppf quotient of an étale equivalence relation is representable,
étale, and surjective when the quotient sheaf has representable diagonal. -/
theorem quotientMap_etale_surjective {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (h_representableDiagonal :
      uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj)) :
    (MorphismProperty.over (@Etale ⊓ @Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map to the fppf quotient of an étale equivalence relation is representable
and étale when the quotient sheaf has representable diagonal. -/
theorem quotientMap_etale {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (h_representableDiagonal :
      uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj)) :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map to the fppf quotient of an étale equivalence relation is representable
and has surjective represented pullbacks when the quotient sheaf has representable diagonal. -/
theorem quotientMap_surjective {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (h_representableDiagonal :
      uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj)) :
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The canonical map to the fppf quotient of an étale equivalence relation is étale-locally
surjective when the quotient sheaf has representable diagonal. -/
theorem quotientMap_locallySurjective {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (h_representableDiagonal :
      uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj)) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- An étale equivalence relation whose fppf quotient has representable diagonal presents
that quotient: the canonical map is representable and étale, is étale-locally surjective,
and has the given relation as its kernel pair. -/
theorem isPresentation_quotientMap {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    (h_representableDiagonal :
      uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj)) :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      IsKernelPair (P.quotientMap (Scheme.fppfTopology.over S))
        ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.t)
        ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.s) := sorry

end AlgebraicGeometry.Scheme.PreRelation
