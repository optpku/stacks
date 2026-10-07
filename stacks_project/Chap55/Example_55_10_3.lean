module
public import stacks_project.Chap55.Example_55_10_3_Conic
public import stacks_project.Chap54.Lemma_54_16_4_Contraction
public import stacks_project.Chap55.Definition_55_8_4_MinimalModel
@[expose] public section
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SplitConic
open scoped AlgebraicGeometry
noncomputable section
universe u
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) [Fact (Irreducible π)]

/-- Example 55.10.3 (1): the explicit Proj model is the closed conic in `ℙ²_R` cut out by
`T₁ * T₂ - π * T₀ ^ 2`. -/
@[stacks 0CA0, instance]
instance splitConicPlaneInclusion_isClosedImmersion :
    IsClosedImmersion (planeInclusion R π) := sorry

/-- Example 55.10.3 (2): the two projective-line coordinates map to the selected pair
`(T₀,T₁)` or `(T₀,T₂)` in the conic coordinate ring. -/
@[stacks 0CA0]
theorem splitConicProjectionRingHom_apply (second : Bool) (i : Fin 2) :
    projectionRingHom R π second (MvPolynomial.X i) =
      Ideal.Quotient.mk (equationIdeal R π).toIdeal
        (MvPolynomial.X (projectionCoordinates second i)) := sorry

/-- Example 55.10.3 (3): the special fibre is the scheme-theoretic union of its two
explicit components. -/
@[stacks 0CA0]
theorem splitConicSpecialFiber_eq_union :
    (toSpec R π).specialFiberIdeal =
      (componentInclusion R π false).ker ⊓ (componentInclusion R π true).ker := sorry

/-- Example 55.10.3 (4): each explicit component is a projective line over the residue field. -/
@[stacks 0CA0]
theorem splitConicComponent_iso_projectiveLine (second : Bool) :
    Nonempty (component R π second ≅
      ProjectiveSpace.scheme
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) 1) := sorry

/-- Example 55.10.3 (5): each component of the special fibre is an exceptional curve of the
first kind. -/
@[stacks 0CA0, instance]
instance splitConicComponent_isExceptionalCurve (second : Bool) :
    IsExceptionalCurveFirstKind ((componentInclusion R π second).ker) := sorry

/-- The explicit split-conic Proj model over a discrete valuation ring is Noetherian. -/
instance splitConicModel_isNoetherian : IsNoetherian (model R π) := sorry

/-- Example 55.10.3 (6): either total projection contracts the opposite exceptional
component to the standard closed point `[1 : 0]`. -/
@[stacks 0CA0]
theorem splitConicProjection_isContraction (second : Bool) :
    IsContraction ((componentInclusion R π (!second)).ker)
      (projection R π second) (projectionCenter R) := sorry

/-- Example 55.10.3 (7): either projection identifies the retained component with the target
special fibre. -/
@[stacks 0CA0, instance]
instance splitConicComponentProjection_isIso (second : Bool) :
    IsIso (componentProjection R π second) := sorry

/-- Example 55.10.3 (8): either projection induces an isomorphism on the generic fibre. -/
@[stacks 0CA0, instance]
instance splitConicGenericFiberProjection_isIso (second : Bool) :
    IsIso (genericFiberProjection R π second) := sorry

/-- Example 55.10.3 (9): the target projective line is a minimal model over the discrete
valuation ring. -/
@[stacks 0CA0, instance]
instance splitConicProjectiveLine_isMinimalModel :
    Scheme.Hom.IsMinimalModel (ProjectiveSpace.toSpec R 1) := sorry

/-- Example 55.10.3 (10): no target automorphism intertwines the two marked contractions, so
the resulting marked minimal models are nonunique. -/
@[stacks 0CA0]
theorem splitConicMinimalModels_nonunique :
    ¬ ∃ e : ProjectiveSpace.scheme R 1 ≅ ProjectiveSpace.scheme R 1,
      projection R π false ≫ e.hom = projection R π true := sorry
