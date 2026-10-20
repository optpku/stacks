module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import ReasLib.AlgebraicGeometry.ChowMotive
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory
public import ReasLib.AlgebraicGeometry.Correspondence.GraphEvaluation
public import ReasLib.AlgebraicGeometry.Correspondence.Transpose
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Monoidal

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents TopologicalSpace
open scoped CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace ChowMotive

open AlgebraicGeometry
open AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- The motive `h(X)` of a smooth projective scheme, with identity projector. -/
def h (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) :=
  (GradedCategory.ofScheme X 0 :
    ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))

/-- The underlying graded object of `h(X)` is `X` in Tate degree zero. -/
theorem h_def (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    h X = (GradedCategory.ofScheme X 0 :
      ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :=
  rfl

/-- The Tate twist `h(X)(n)` of the motive of `X`. -/
def tateTwist (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (n : ℤ) : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) :=
  (GradedCategory.ofScheme X n :
    ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))

/-- The underlying graded object of `h(X)(n)` is `X` in Tate degree `n`. -/
theorem tateTwist_def (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (n : ℤ) : tateTwist X n = (GradedCategory.ofScheme X n :
      ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :=
  rfl

/-- The point is equidimensional. -/
instance point_equidimensional : EquidimensionalSpace (SchemeOverField.point k).left := sorry

/-- The point has topological Krull dimension zero. -/
theorem point_dimension :
    topologicalKrullDim (SchemeOverField.point k).left = (0 : WithBot ℕ∞) := sorry

/-- A product of equidimensional smooth projective schemes is equidimensional. -/
instance product_equidimensional (X Y : Correspondence.Category k)
    [EquidimensionalSpace X.scheme.left] [EquidimensionalSpace Y.scheme.left] :
    EquidimensionalSpace (Correspondence.Category.product X Y).scheme.left := sorry

/-- Dimensions of equidimensional smooth projective schemes add under product. -/
theorem product_dimension (X Y : Correspondence.Category k)
    [EquidimensionalSpace X.scheme.left] [EquidimensionalSpace Y.scheme.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.scheme.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.scheme.left = (e : WithBot ℕ∞)) :
    topologicalKrullDim (Correspondence.Category.product X Y).scheme.left =
      (d + e : ℕ) := sorry

/-- Equidimensionality of a scheme is retained when it is placed in the correspondence
category via `GradedCategory.ofScheme`. -/
instance ofScheme_equidimensional (X : SchemeOverField k) [Smooth X.hom]
    [Projective X.hom] [EquidimensionalSpace X.left] :
    EquidimensionalSpace (GradedCategory.ofScheme X 0).1.scheme.left :=
  (GradedCategory.ofScheme_scheme X 0).symm ▸ ‹EquidimensionalSpace X.left›

/-- The degree of the transpose of the fundamental correspondence is zero. -/
theorem transposeFundamental_degree (d : ℕ) :
    (d : ℤ) - 0 + -(d : ℤ) = 0 := by
  omega

/-- The transpose of the diagonal graph has degree `d`. -/
theorem transposeDiagonal_degree (d : ℕ) :
    ((d + d : ℕ) : ℤ) - (d : ℤ) + 0 = d := by
  omega

/-- Adding a zero correspondence degree does not change the degree. -/
theorem zero_add_degree (d : ℤ) : 0 + d = d := by
  omega

/-- The transpose of the fundamental class is the degree-zero correspondence from the
point to `X`. -/
def pointToScheme (X : Correspondence.Category k) [EquidimensionalSpace X.scheme.left]
    (d : ℕ) (hXdim : topologicalKrullDim X.scheme.left = (d : WithBot ℕ∞)) :
    Correspondence.Rational (SchemeOverField.point k) X.scheme 0 :=
  Correspondence.castDegree (transposeFundamental_degree d)
    (Correspondence.transpose X.scheme (SchemeOverField.point k) d 0 hXdim
      point_dimension (-(d : ℤ)) (Correspondence.fundamental X d))

/-- The transpose of the diagonal graph, as a degree-`d` correspondence from `X` to
`X × X`. -/
def schemeToDiagonal (X : Correspondence.Category k)
    [EquidimensionalSpace X.scheme.left]
    (d : ℕ) (hXdim : topologicalKrullDim X.scheme.left = (d : WithBot ℕ∞)) :
    Correspondence.Rational X.scheme
      (Correspondence.Category.product X X).scheme (d : ℤ) :=
  Correspondence.castDegree
    (transposeDiagonal_degree d)
    (Correspondence.transpose (Correspondence.Category.product X X).scheme X.scheme
      (d + d) d (product_dimension X X d d hXdim hXdim) hXdim 0
      (Correspondence.graphOfDiagonal X))

/-- The coevaluation correspondence induced by the diagonal class of `X`. -/
def diagonalCoevaluationCorrespondence (X : Correspondence.Category k)
    [EquidimensionalSpace X.scheme.left]
    (d : ℕ) (hXdim : topologicalKrullDim X.scheme.left = (d : WithBot ℕ∞)) :
    Correspondence.Rational (SchemeOverField.point k)
      (Correspondence.Category.product X X).scheme (d : ℤ) :=
  Correspondence.castDegree (zero_add_degree d)
    (Correspondence.composition (SchemeOverField.point k) X.scheme
      (Correspondence.Category.product X X).scheme 0 d
      (pointToScheme X d hXdim) (schemeToDiagonal X d hXdim))

/-- The evaluation correspondence induced by the diagonal class of `X`. -/
def diagonalEvaluationCorrespondence (X : Correspondence.Category k) (d : ℕ) :
    Correspondence.Rational (Correspondence.Category.product X X).scheme
      (SchemeOverField.point k) (-(d : ℤ)) :=
  Correspondence.castDegree (zero_add_degree (-(d : ℤ)))
    (Correspondence.composition (Correspondence.Category.product X X).scheme X.scheme
      (SchemeOverField.point k) 0 (-(d : ℤ))
      (Correspondence.graphOfDiagonal X) (Correspondence.fundamental X d))

/-- Degree transport from the diagonal coevaluation class to the graded Hom degree. -/
theorem diagonalCoevaluation_degree (d : ℕ) :
    (d : ℤ) = ((0 : ℤ) + d) - 0 := by
  omega

/-- Degree transport from the diagonal evaluation class to the graded Hom degree. -/
theorem diagonalEvaluation_degree (d : ℕ) :
    -(d : ℤ) = 0 - ((d : ℤ) + 0) := by
  omega

/-- The coevaluation morphism `𝟙 ⟶ h(X) ⊗ h(X)(d)` represented by the diagonal class. -/
def diagonalCoevaluation (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left]
    (d : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) :
    𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) ⟶
      h X ⊗ tateTwist X d where
  f := Correspondence.castDegree (diagonalCoevaluation_degree d)
    (diagonalCoevaluationCorrespondence (GradedCategory.ofScheme X 0).1 d
      ((GradedCategory.ofScheme_scheme X 0).symm ▸ hXdim))
  comm := sorry

/-- The evaluation morphism `h(X)(d) ⊗ h(X) ⟶ 𝟙` represented by the diagonal class. -/
def diagonalEvaluation (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (d : ℕ) : tateTwist X d ⊗ h X ⟶
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) where
  f := Correspondence.castDegree (diagonalEvaluation_degree d)
    (diagonalEvaluationCorrespondence (GradedCategory.ofScheme X 0).1 d)
  comm := sorry

/-- The exact pairing whose two morphisms are the diagonal class of `X`. -/
@[implicit_reducible]
def exactPairing (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    (d : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) :
    ExactPairing (h X) (tateTwist X d) where
  coevaluation' := diagonalCoevaluation X d hXdim
  evaluation' := diagonalEvaluation X d
  coevaluation_evaluation' := sorry
  evaluation_coevaluation' := sorry

end ChowMotive
