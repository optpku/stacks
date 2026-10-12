/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Tensor
public import ReasLib.AlgebraicGeometry.Correspondence.Graph
public import ReasLib.AlgebraicGeometry.Correspondence.Transpose
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Separated.Product

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- The graph correspondence of the diagonal morphism `X ⟶ X ⨯ X`. -/
def graphOfDiagonal (X : Category k) :
    Rational (Category.product X X).scheme X.scheme 0 :=
  @rationalGraph k _ (Category.product X X).scheme X.scheme inferInstance inferInstance
    (let _ : Projective (Category.product X X).scheme.hom := inferInstance
     let _ : LocallyProjective (Category.product X X).scheme.hom := inferInstance
     let _ : IsProper (Category.product X X).scheme.hom := inferInstance
     inferInstance)
    (Limits.prod.lift (𝟙 X.scheme) (𝟙 X.scheme) ≫
      eqToHom (Category.scheme_product X X).symm)

/-- The diagonal graph correspondence is the rational graph of the diagonal morphism. -/
theorem graphOfDiagonal_def (X : Category k) :
    graphOfDiagonal X =
      @rationalGraph k _ (Category.product X X).scheme X.scheme inferInstance inferInstance
        (let _ : Projective (Category.product X X).scheme.hom := inferInstance
         let _ : LocallyProjective (Category.product X X).scheme.hom := inferInstance
         let _ : IsProper (Category.product X X).scheme.hom := inferInstance
         inferInstance)
        (Limits.prod.lift (𝟙 X.scheme) (𝟙 X.scheme) ≫
          eqToHom (Category.scheme_product X X).symm) :=
  rfl

/-- The fundamental class of an equidimensional smooth projective scheme as a
correspondence to `Spec(k)`. -/
noncomputable def fundamental (X : Category k) (d : ℕ) :
    Rational X.scheme (SchemeOverField.point k) (-(d : ℤ)) :=
  let hBase : IsLocallyNoetherian (Spec (CommRingCat.of k)) :=
    @UniversallyCatenary.toIsLocallyNoetherian _
      (@instUniversallyCatenarySpec k _
        (@instUniversallyCatenaryRingOfField.{u, u} k _))
  let hX : IsLocallyNoetherian X.scheme.left :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ X.scheme.hom inferInstance hBase
  homologyEquiv X.scheme (-(d : ℤ))
    (castHomologyDegree (neg_neg (d : ℤ)).symm
      ((1 : ℚ) ⊗ₜ[ℤ]
        (@chowClass X.scheme.left hX
          (X.scheme.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (d : ℤ)
          (@CycleGroup.fundamental X.scheme.left hX
            (X.scheme.hom.relativeDimensionFunction (fun _ ↦ 0)) (d : ℤ)))))

/-- The fundamental correspondence is the image of the rationalized fundamental Chow
class under `homologyEquiv`. -/
theorem fundamental_def (X : Category k) (d : ℕ) :
    fundamental X d =
      let hBase : IsLocallyNoetherian (Spec (CommRingCat.of k)) :=
        @UniversallyCatenary.toIsLocallyNoetherian _
          (@instUniversallyCatenarySpec k _
            (@instUniversallyCatenaryRingOfField.{u, u} k _))
      let hX : IsLocallyNoetherian X.scheme.left :=
        @LocallyOfFiniteType.isLocallyNoetherian _ _ X.scheme.hom inferInstance hBase
      homologyEquiv X.scheme (-(d : ℤ))
        (castHomologyDegree (neg_neg (d : ℤ)).symm
          ((1 : ℚ) ⊗ₜ[ℤ]
            (@chowClass X.scheme.left hX
              (X.scheme.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (d : ℤ)
              (@CycleGroup.fundamental X.scheme.left hX
                (X.scheme.hom.relativeDimensionFunction (fun _ ↦ 0)) (d : ℤ))))) :=
  rfl

/-- The degree of the upper evaluation path simplifies to `-e`. -/
theorem graphTranspose_upperDegree (e : ℕ) :
    (((0 + 0 : ℤ) + 0) + (-(e : ℤ))) = -(e : ℤ) := by
  ring

/-- The degree of the lower evaluation path simplifies to `-e`. -/
theorem graphTranspose_lowerDegree (d e : ℕ) :
    (((0 + ((d : ℤ) - (e : ℤ) + 0)) + 0) + (-(d : ℤ))) = -(e : ℤ) := by
  ring

/-- For a morphism `f : Y ⟶ X` of smooth projective equidimensional schemes, the two
evaluation composites formed from the graph of `f`, its transpose, the diagonal graphs,
and the fundamental classes agree as correspondences from `X ⨯ Y` to `Spec(k)`. -/
theorem graphTranspose_commutes (X Y : Category k)
    [EquidimensionalSpace X.scheme.left] [EquidimensionalSpace Y.scheme.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.scheme.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.scheme.left = (e : WithBot ℕ∞))
    (f : Y.scheme ⟶ X.scheme) :
    let a := rationalGraph f
    let aT := transpose X.scheme Y.scheme d e hXdim hYdim 0 a
    castDegree (graphTranspose_upperDegree e)
        (composition (Category.product X Y).scheme Y.scheme (SchemeOverField.point k)
          ((0 + 0 : ℤ) + 0) (-(e : ℤ))
          (composition (Category.product X Y).scheme (Category.product Y Y).scheme Y.scheme
            (0 + 0) 0 (tensor a (correspondenceId Y)) (graphOfDiagonal Y))
          (fundamental Y e)) =
      castDegree (graphTranspose_lowerDegree d e)
        (composition (Category.product X Y).scheme X.scheme (SchemeOverField.point k)
          ((0 + ((d : ℤ) - (e : ℤ) + 0)) + 0) (-(d : ℤ))
          (composition (Category.product X Y).scheme (Category.product X X).scheme X.scheme
            (0 + ((d : ℤ) - (e : ℤ) + 0)) 0
            (tensor (correspondenceId X) aT) (graphOfDiagonal X))
          (fundamental X d)) := sorry

end AlgebraicGeometry.Correspondence
