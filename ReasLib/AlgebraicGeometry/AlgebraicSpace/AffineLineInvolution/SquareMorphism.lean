module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.AffineSpace.AdditiveGroup
public import ReasLib.AlgebraicGeometry.AffineSpace.SquareMap
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Representability
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-!
# The descended square morphism of the affine-line involution space

The morphism `X ⟶ 𝔸¹_k` induced by `x ↦ x²` on the atlas of the affine-line
involution space is an isomorphism away from `0`, has a unique field-valued point
over `0`, is universally injective, and is not separated in characteristic different from two.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-- The endomorphism of the affine-line atlas sending the coordinate to its square. -/
def squareOver (k : Type u) [Field k] : cover k ⟶ cover k :=
  Over.homMk (AffineSpace.squareMap k) (AffineSpace.squareMap_over k)

/-- The underlying scheme morphism of `squareOver` is the affine-line squaring map. -/
theorem squareOver_left (k : Type u) [Field k] :
    (squareOver k).left = AffineSpace.squareMap k := sorry

/-- Squaring equalizes the two projections of the involution relation, since
`x² = (-x)²`. -/
theorem squareOver_equalizes (k : Type u) [Field k] :
    (preRelation k).t ≫ squareOver k = (preRelation k).s ≫ squareOver k := sorry

/-- The origin `Spec k` of the affine line, viewed as a scheme over `Spec k`. -/
def originOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk (AffineSpace.zeroLeft (ULift.{u} (Fin 1)) (base k) ≫ (cover k).hom)

/-- `originOver` is the zero section of the affine line, viewed in `Over (Spec k)`. -/
theorem originOver_eq (k : Type u) [Field k] :
    originOver k =
      Over.mk (AffineSpace.zeroLeft (ULift.{u} (Fin 1)) (base k) ≫ (cover k).hom) := sorry

/-- The origin morphism `Spec k ⟶ 𝔸¹_k` over `Spec k`. -/
def originToCover (k : Type u) [Field k] : originOver k ⟶ cover k :=
  Over.homMk (AffineSpace.zeroLeft (ULift.{u} (Fin 1)) (base k))

/-- The underlying scheme morphism of `originToCover` is the zero section of the affine line. -/
theorem originToCover_left (k : Type u) [Field k] :
    (originToCover k).left = AffineSpace.zeroLeft (ULift.{u} (Fin 1)) (base k) := sorry

/-- The descended morphism `X ⟶ 𝔸¹_k` induced by `x ↦ x²` on the atlas. -/
def toAffineLine (k : Type u) [Field k] :
    sheafOfPoints k ⟶
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k) :=
  (preRelation k).quotientSheafDesc (Scheme.fppfTopology.over (base k))
    (squareOver k) (squareOver_equalizes k)

/-- `toAffineLine` is the canonical quotient-sheaf descent of `squareOver`. -/
theorem toAffineLine_eq (k : Type u) [Field k] :
    toAffineLine k =
      (preRelation k).quotientSheafDesc (Scheme.fppfTopology.over (base k))
        (squareOver k) (squareOver_equalizes k) := sorry

/-- On the atlas, `toAffineLine` recovers the squaring map `x ↦ x²`. -/
theorem toAffineLine_comp_atlas (k : Type u) [Field k] :
    atlas k ≫ toAffineLine k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (squareOver k) := sorry

/-- `toAffineLine` is an isomorphism after base change along `D(x) ⟶ 𝔸¹_k`. -/
@[instance]
theorem isIso_over_punctured (k : Type u) [Field k] [NeZero (2 : k)] :
    IsIso
      (pullback.snd (toAffineLine k)
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (puncturedι k))) :=
  sorry

/-- The fibre over the origin has exactly one point over every field-valued object
over `Spec k`. -/
theorem unique_point_over_origin (k : Type u) [Field k] [NeZero (2 : k)]
    (K : Type u) [Field K] (σ : Spec (CommRingCat.of K) ⟶ base k) :
    Nonempty
        ((pullback (toAffineLine k)
            ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
              (originToCover k))).obj.obj
          (op (Over.mk σ))) ∧
      Subsingleton
        ((pullback (toAffineLine k)
            ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
              (originToCover k))).obj.obj
          (op (Over.mk σ))) :=
  sorry

/-- The relative diagonal of `toAffineLine` is a representable surjection, so the
morphism is universally injective. -/
theorem universallyInjective_toAffineLine (k : Type u) [Field k] [NeZero (2 : k)] :
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{u + 1}
      (pullback.diagonal (toAffineLine k)).hom := sorry

/-- The relative diagonal of `toAffineLine` is not a closed immersion, so the
morphism is not separated. -/
theorem not_separated_toAffineLine (k : Type u) [Field k] [NeZero (2 : k)] :
    ¬ (MorphismProperty.over (@IsClosedImmersion)).relative uliftYoneda.{u + 1}
        (pullback.diagonal (toAffineLine k)).hom := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
