/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Etale

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The fppf quotient sheaf of an étale equivalence relation on a scheme over a base
scheme has representable diagonal. -/
@[stacks 02WW]
theorem quotientSheaf_representableDiagonal {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    uliftYoneda.{u + 1}.relativelyRepresentable
      (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj) := sorry

/-- The canonical map from a scheme to the fppf quotient of an étale equivalence
relation is representable, étale, and surjective. -/
@[stacks 02WW]
theorem etale_surjective_quotientMap {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    (MorphismProperty.over (@Etale ⊓ @Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := by
  exact P.quotientMap_etale_surjective P.quotientSheaf_representableDiagonal

/-- The canonical map `U ⟶ U/R` is relatively representable with respect to
`uliftYoneda`. -/
theorem quotientMap_relativelyRepresentable {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    uliftYoneda.{u + 1}.relativelyRepresentable
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := by
  exact P.etale_surjective_quotientMap.rep

/-- The canonical map `U ⟶ U/R` is representable and étale with respect to
`uliftYoneda`. -/
theorem etale_quotientMap {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := by
  exact MorphismProperty.relative_monotone
    (P := MorphismProperty.over (@Etale ⊓ @Surjective)) (fun _ _ _ h ↦ h.1) _
    P.etale_surjective_quotientMap

/-- Represented pullbacks of the canonical map `U ⟶ U/R` are surjective morphisms of
schemes over `S`. -/
theorem surjective_quotientMap {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{u + 1}
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := by
  exact MorphismProperty.relative_monotone
    (P := MorphismProperty.over (@Etale ⊓ @Surjective)) (fun _ _ _ h ↦ h.2) _
    P.etale_surjective_quotientMap

/-- The canonical map `U ⟶ U/R` is étale-locally surjective. -/
theorem locallySurjective_quotientMap {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (P.quotientMap (Scheme.fppfTopology.over S)).hom := by
  have hq := P.etale_surjective_quotientMap
  refine ⟨fun {T} x ↦ ?_⟩
  let ξ : uliftYoneda.{u + 1}.obj T ⟶
      (P.quotientSheaf (Scheme.fppfTopology.over S)).obj := uliftYonedaEquiv.symm x
  obtain ⟨V, g, f, h⟩ := hq.rep ξ
  have hg := hq.property ξ f g h
  have hmem : Presheaf.imageSieve
      (P.quotientMap (Scheme.fppfTopology.over S)).hom x g := by
    refine ⟨uliftYonedaEquiv f, ?_⟩
    rw [← uliftYonedaEquiv_comp, h.w]
    simpa only [ξ, Quiver.Hom.unop_op, Equiv.apply_symm_apply] using
      (uliftYonedaEquiv_naturality ξ g.op).symm
  have hcover : Sieve.ofArrows (fun _ : PUnit.{u + 1} ↦ V) (fun _ ↦ g) ∈
      (Scheme.etaleTopology.over S) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (Scheme.Cover.mkOfCovers (P := @Etale) PUnit.{u + 1} (fun _ ↦ V.left)
      (fun _ ↦ g.left) (fun x ↦ by
        obtain ⟨y, hy⟩ := hg.2.surj x
        exact ⟨PUnit.unit, y, hy⟩) (fun _ ↦ hg.1)).mem_grothendieckTopology
  apply (Scheme.etaleTopology.over S).superset_covering ?_ hcover
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  exact hmem

/-- The fppf quotient sheaf `U/R` of an étale equivalence relation on a scheme over `S`
is an algebraic space at the sheaf layer: it has representable diagonal, and the
canonical atlas `U ⟶ U/R` is representable étale and étale-locally surjective. -/
theorem quotientSheaf_spec {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (P.quotientSheaf (Scheme.fppfTopology.over S)).obj) ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (P.quotientMap (Scheme.fppfTopology.over S)).hom := by
  exact ⟨P.quotientSheaf_representableDiagonal, P.etale_quotientMap,
    P.locallySurjective_quotientMap⟩

/-- The data `(U, P, U ⟶ U/R)` is a presentation of `U/R` at the `uliftYoneda`/sheaf
layer: `P` is an étale equivalence relation, the atlas is étale and étale-locally
surjective, and the two projections of `P` form the kernel pair of the atlas. -/
theorem isPresentation_quotientSheaf {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    P.IsEtaleEquivalenceRelation ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (P.quotientMap (Scheme.fppfTopology.over S)).hom ∧
      IsKernelPair (P.quotientMap (Scheme.fppfTopology.over S))
        ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.t)
        ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.s) := by
  letI := IsEtaleEquivalenceRelation.isEquivalenceRelation (P := P)
  exact ⟨inferInstance, P.etale_quotientMap, P.locallySurjective_quotientMap,
    P.isKernelPair_quotientMap⟩

end AlgebraicGeometry.Scheme.PreRelation
