import AnnalsChallenge.Tests.UniformMordellLangSemantics

/- These guards inspect specifications below the wrappers: predicate fields,
the precise cohomology used for genus, and the functor represented by Jac.
They check elaborated specifications, not the truth of admitted proofs. -/
set_option autoImplicit false

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.JacobianChallenge Opposite TopologicalSpace
universe u

section PredicateFields

variable {k : Type u} [Field k] (C : Over (Spec (.of k))) [hC : Curve C]

-- A `Curve` witness contains actual integrality, separatedness, finite type,
-- and Krull dimension one, rather than an empty marker proposition.
example : IsIntegral C.left := hC.toVariety.toIsIntegral
example : IsSeparated C.hom := hC.toVariety.toIsSeparated
example : Scheme.Hom.FiniteType C.hom := hC.toVariety.toFiniteType
example : topologicalKrullDim C.left = 1 := hC.topologicalKrullDim_eq_one

variable {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)
variable [hf : IsFiniteLocallyFreeOfRank f d]

-- Hilbert degree records finite locally free STRUCTURE MODULE rank.
-- It is not the rank of the divisor's ideal module.
example : IsAffineHom f := hf.toIsFiniteLocallyFree.toIsAffineHom
example : Scheme.Modules.IsFiniteLocallyFree f.pushforwardStructureModule :=
  hf.toIsFiniteLocallyFree.pushforward_isFiniteLocallyFree
example : Scheme.Modules.IsFiniteLocallyFreeOfRank d f.pushforwardStructureModule :=
  hf.pushforward_isFiniteLocallyFreeOfRank

end PredicateFields

section GeometricSpecifications

variable {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]

local instance : Curve C := CurveJacobian.PicardConstruction.targetCurve C
local instance : (RelativePicard.degreeSubfunctor C 0).toFunctor.IsRepresentable :=
  CurveJacobian.PicardConstruction.degreeZeroRepresentable C

-- Expand the numerical invariant all the way to right-derived global evaluation,
-- with the scalar action induced by the structure map of C.
example : genus C = by
    letI := CurveJacobian.genusInjectiveResolutions C.left
    letI := CurveJacobian.genusEvaluationAdditive C.left
    let H1 := ((SheafOfModules.evaluation C.left.ringCatSheaf
      (op (⊤ : Opens C.left))).rightDerived 1).obj
        (SheafOfModules.unit C.left.ringCatSheaf)
    exact Module.finrank k
      ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap C.hom)).obj H1) := rfl

-- Representability at EVERY test scheme; no rational point of C is assumed.
example : (RelativePicard.degreeSubfunctor C 0).toFunctor.RepresentableBy (Jacobian C) :=
  RelativePicard.componentRepresentation C 0

example (T : Over (Spec (.of k))) :
    (T ⟶ Jacobian C) ≃ (RelativePicard.degreeSubfunctor C 0).obj (op T) :=
  (RelativePicard.componentRepresentation C 0).homEquiv

-- Read the implemented relative Picard presheaf down to tensor-invertible
-- isomorphism classes on the fiber product.
example (T : Over (Spec (.of k))) :
    (RelativePicard.presheaf C).obj (op T) = (T ⊗ C).left.PicardGroup := rfl

-- The sheafification is fppf, rather than equality with the unsheafified values.
example : (RelativePicard.functor C).obj =
    (Scheme.fppfTopology.over (Spec (.of k))).sheafify (RelativePicard.presheaf C) := rfl

-- The degree locus uses the unit of that SAME concrete sheafification.
example (d : ℤ) : RelativePicard.degreeSubfunctor C d =
    ((RelativePicard.degreePresheaf C d).image
      (GrothendieckTopology.toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
        (RelativePicard.presheaf C))).sheafify
      (Scheme.fppfTopology.over (Spec (.of k))) := rfl

-- The universal divisor class enters Picard through that same concrete unit,
-- without an admitted equality between two choices of sheafification model.
example (d : ℕ) : RelativePicard.abelSection C d =
    (GrothendieckTopology.toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
      (RelativePicard.presheaf C)).app _ (RelativePicard.abelPicardClass C d) := rfl

-- The full group object comes from the represented degree-zero Picard group.
example : Jacobian.instGrpObj (C := C) =
    GrpObj.ofRepresentableBy (RelativePicard.component C 0)
      (RelativePicard.degreeZeroGroupFunctor C)
      (RelativePicard.degreeZeroGroupRepresentation C) := rfl

-- A Hilbert point built from x contains the actual kernel of its graph.
example {T : Over (Spec (.of k))} (x : T ⟶ C) :
    (Hilbert.Point.ofSection x).ideal = (Hilbert.sectionGraph x).ker := rfl

-- The base-change requirement is genuinely quantified over all further tests.
example (d : ℤ) (T : (Over (Spec (.of k)))ᵒᵖ)
    (x : (RelativePicard.presheaf C).obj T) :
    x ∈ (RelativePicard.degreePresheaf C d).obj T ↔
      ∀ (T' : (Over (Spec (.of k)))ᵒᵖ) (f : T ⟶ T'),
        RelativePicard.relativeDegree C T' ((RelativePicard.presheaf C).map f x) =
          fun _ ↦ d := Iff.rfl

-- The sign of normalization is [variable graph] * [constant P graph]^{-1}.
example (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    CurveJacobian.PicardConstruction.normalizedClass C P =
      CurveJacobian.PicardConstruction.sectionGroupClass C (𝟙 C) *
        (CurveJacobian.PicardConstruction.sectionGroupClass C
          (CartesianMonoidalCategory.toUnit C ≫ P))⁻¹ := rfl

end GeometricSpecifications

-- Infinite rational-point sets give infinity, rather than the default 0 of
-- Nat.card. These guards do not assume Faltings' theorem.
example {α : Type u} [Infinite α] : ENat.card α = ⊤ :=
  ENat.card_eq_top_of_infinite

-- The rank used is the free rank after quotienting by torsion.
example (G : Type u) [CommGroup G] [Group.FG G] :
    CommGroup.freeRank G = Group.rank (G ⧸ CommGroup.torsion G) := rfl

-- Round-up to a natural bound does not accidentally introduce a dependence
-- on F, C, or P: c has only these two natural arguments.
example : ℕ → ℕ → ℕ := UniformMordellLang.c

#print axioms AlgebraicGeometry.JacobianChallenge.genus
#print axioms AlgebraicGeometry.RelativePicard.functor_val
