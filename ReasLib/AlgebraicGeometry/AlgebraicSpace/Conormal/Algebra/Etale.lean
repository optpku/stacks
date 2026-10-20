module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Map.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Pullback.Composition

/-!
# Étale restriction of conormal algebras

The canonical flat-base-change map identifies the conormal algebra of an
immersion with that of its pullback to an étale scheme chart, compatibly with
homogeneous components and morphisms of charts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra

variable {S : Scheme.{u}}

/-- Pullback of the total conormal algebra agrees with its inverse-image pushout
presentation, by interchanging the two pushout legs. -/
def pullbackTotalIso {Y Z X : AlgebraicSpace S} (f : Y ⟶ Z)
    (i : Z ⟶ X) [IsImmersion i] :
    (QcAlgebraUnder.pullback f).obj (total i) ≅ pullback f i :=
  ObjectProperty.isoMk _ (Under.isoMk
    (pushoutSymmetry ((commRingInverseImage f).map (structureMap i))
      (inverseImageStructureSheafHom f))
    (inr_comp_pushoutSymmetry_hom _ _))

variable {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
variable {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]

/-- The canonical algebra map comparing an immersion with its pullback to an
étale scheme chart. -/
def restrictEtaleHom :
    (QcAlgebraUnder.pullback (Hom.Conormal.toZ i φ)).obj (total i) ⟶
      total (Hom.Conormal.ι i φ) :=
  (pullbackTotalIso (Hom.Conormal.toZ i φ) i).hom ≫
    map (IsPullback.of_hasPullback i φ).toCommSq

/-- Pullback to an étale scheme chart canonically identifies the total conormal
algebra of an immersion with the total conormal algebra of its base change. -/
def restrictEtale :
    (QcAlgebraUnder.pullback (Hom.Conormal.toZ i φ)).obj (total i) ≅
      total (Hom.Conormal.ι i φ) :=
  pullbackTotalIso (Hom.Conormal.toZ i φ) i ≪≫
    @asIso _ _ _ _ (map (IsPullback.of_hasPullback i φ).toCommSq)
      (map_isIso_of_isPullback_of_flat (IsPullback.of_hasPullback i φ))

/-- The forward component of the étale comparison is the canonical algebra map. -/
@[simp]
theorem restrictEtale_hom :
    (restrictEtale i φ).hom = restrictEtaleHom i φ :=
  rfl

/-- Successive pullbacks of a total conormal algebra along a morphism of charts
and the projection to the immersed space agree with the direct pullback. -/
def restrictEtaleToZReassoc {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (QcAlgebraUnder.pullback (Hom.Conormal.spaceMap i φ ψ f hf)).obj
        ((QcAlgebraUnder.pullback (Hom.Conormal.toZ i ψ)).obj (total i)) ≅
      (QcAlgebraUnder.pullback (Hom.Conormal.toZ i φ)).obj (total i) :=
  (QcAlgebraUnder.pullbackComp (Hom.Conormal.spaceMap i φ ψ f hf)
      (Hom.Conormal.toZ i ψ)).app (total i) ≪≫
    (QcAlgebraUnder.pullbackCongr
      (Hom.Conormal.spaceMap_comp_toZ i φ ψ f hf)).app (total i)

/-- A morphism of étale scheme charts induces the canonical comparison of the
conormal algebras of the corresponding pulled-back immersions. -/
def restrictEtaleChartMap {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (QcAlgebraUnder.pullback (Hom.Conormal.spaceMap i φ ψ f hf)).obj
        (total (Hom.Conormal.ι i ψ)) ⟶ total (Hom.Conormal.ι i φ) :=
  (pullbackTotalIso (Hom.Conormal.spaceMap i φ ψ f hf) (Hom.Conormal.ι i ψ)).hom ≫
    map (Hom.Conormal.chartSq i φ ψ f hf)

/-- The canonical étale comparison of total conormal algebras is functorial in
morphisms of étale scheme charts over the ambient algebraic space. -/
theorem restrictEtale_natural {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (QcAlgebraUnder.pullback (Hom.Conormal.spaceMap i φ ψ f hf)).map
          (restrictEtale i ψ).hom ≫ restrictEtaleChartMap i φ ψ f hf =
      (restrictEtaleToZReassoc i φ ψ f hf).hom ≫ (restrictEtale i φ).hom :=
  sorry

/-- Étale base change identifies every homogeneous component of the conormal
algebra by the canonical homogeneous comparison map. -/
def restrictEtalePiece (n : ℕ) :
    (Modules.pullback (Hom.Conormal.toZ i φ)).obj (piece i n) ≅
      piece (Hom.Conormal.ι i φ) n :=
  @asIso _ _ _ _ (mapPiece (IsPullback.of_hasPullback i φ).toCommSq n)
    (mapPiece_isIso_of_isPullback_of_flat (IsPullback.of_hasPullback i φ) n)

/-- The total-algebra étale comparison induces the canonical comparison on every
homogeneous component, compatibly with its inclusion into the total algebra. -/
theorem restrictEtale_graded (n : ℕ) :
    pullbackDegreeToTotal (Hom.Conormal.toZ i φ) i n ≫
        QcAlgebraUnder.underlyingModuleMap
          ((pullbackTotalIso (Hom.Conormal.toZ i φ) i).inv ≫ (restrictEtale i φ).hom) =
      mapPiece (IsPullback.of_hasPullback i φ).toCommSq n ≫
        degreeToTotal (Hom.Conormal.ι i φ) n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra
