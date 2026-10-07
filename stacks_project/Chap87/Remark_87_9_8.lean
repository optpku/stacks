module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap03.Lemma_3_9_2_ObjectProperty
public import stacks_project.Chap03.Lemma_3_9_4_Size
public import stacks_project.Chap87.Lemma_87_2_1_Size
public import stacks_project.Chap87.Lemma_87_10_3_Types
public import stacks_project.Chap87.Remark_87_9_8_Affine
public import stacks_project.Chap87.Remark_87_9_8_Comparison

/-!
# Remark 87.9.8

Over a terminal base, the functor of points of an EGA affine formal scheme
`Spf(A)` is the fppf-sheaf colimit of `h_Spec(A ⧸ I)` as `I` runs over ideals
of definition. Hence it is a classical affine formal algebraic space, and the
category of affine EGA formal schemes is equivalent to the category of
classical affine formal algebraic spaces.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

namespace AlgebraicGeometry.FormalScheme

/-- Remark 87.9.8 (1): over a terminal base, the functor of points of
`ofSpf A` is a colimit of `h_Spec(A ⧸ I)` as `I` runs over ideals of
definition of the admissible topological ring `A`. -/
@[stacks 0AIE]
theorem isColimit_ofSpfCocone (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u})
    (hA : TopologicalRing.IsAdmissibleRing A) :
    ∃ c : Cocone (ofSpfIdealOfDefinitionDiagram 𝒮 S hS A),
      Nonempty (IsColimit c) ∧
        Nonempty (c.pt ≅ (sheafOfPoints 𝒮 S).obj (ofSpf A hA)) :=
  sorry

/-- Remark 87.9.8 (2): over a terminal base, the functor of points of
`ofSpf A` is a classical affine formal algebraic space, provided the chosen
site is a `Sch_α` as in Lemma 87.2.1 and the size of `ofSpf A` is bounded by
some scheme in the site. -/
@[stacks 0AIE]
theorem isClassicalAffine_sheafOfPoints_ofSpf
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A)
    (hsize : ∃ T : 𝒮.carrier, (ofSpf A hA).size ≤ (𝒮.toScheme.obj T).size) :
    IsClassicalAffine ((sheafOfPoints 𝒮 S).obj (ofSpf A hA)) :=
  sorry

/-- Remark 87.9.8 (3): over a terminal base, morphisms of affine EGA formal
schemes are identified with morphisms of their functors of points, provided
the chosen site is a `Sch_α` as in Lemma 87.2.1 and the size of the source is
bounded by the size of some scheme in the site. -/
@[stacks 0AIE]
theorem sheafOfPoints_map_bijective (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    {X Y : FormalScheme.{u}} [IsAffine X] [IsAffine Y]
    (hX : ∃ T, X.size ≤ (𝒮.toScheme.obj T).size) :
    Function.Bijective
      ((sheafOfPoints 𝒮 S).map :
        (X ⟶ Y) → ((sheafOfPoints 𝒮 S).obj X ⟶ (sheafOfPoints 𝒮 S).obj Y)) :=
  sorry

/-- Remark 87.9.8 (4): over a terminal base, every classical affine formal
algebraic space is isomorphic to the functor of points of an affine EGA
formal scheme. -/
@[stacks 0AIE]
theorem exists_isAffine_iso_sheafOfPoints (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (F : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsClassicalAffine F] :
    ∃ (X : FormalScheme.{u}) (_ : IsAffine X),
      Nonempty ((sheafOfPoints 𝒮 S).obj X ≅ F) :=
  sorry

end AlgebraicGeometry.FormalScheme
