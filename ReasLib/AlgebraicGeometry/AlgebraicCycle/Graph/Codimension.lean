module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Graph
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Support
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.Topology.KrullDimension.PureCodimension

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/-- For a morphism of smooth projective schemes, the part of its graph over a clopen
equidimensional stratum of dimension `d` has pure codimension `d`. -/
theorem graph_hasPureCodimension
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (Xd : ℕ → X.left.Opens) (hcover : iSup Xd = ⊤)
    (hdisjoint : Pairwise (fun d e ↦ Disjoint (Xd d : Set X.left) (Xd e : Set X.left)))
    (hclopen : ∀ d, IsClopen (Xd d : Set X.left))
    (hequidimensional : ∀ d, EquidimensionalSpace (Xd d))
    (hdimension : ∀ d, (Xd d : Set X.left).Nonempty →
      topologicalKrullDim (Xd d) = (d : WithBot ℕ∞))
    (f : Y ⟶ X) :
    ∀ d, HasPureCodimension
      (Set.range (SchemeOverField.graph f).base ∩
        (pullback.fst X.hom Y.hom).base ⁻¹' (Xd d : Set X.left)) d := sorry

/-- A cycle on `X ×ₖ Y` is a degree-zero correspondence when its geometric support has pure
codimension `d` over every clopen equidimensional stratum `Xd d` of `X`. -/
def IsDegreeZeroCorrespondence
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    (Xd : ℕ → X.left.Opens)
    (α : AlgebraicCycle (pullback X.hom Y.hom) ℤ) : Prop :=
  ∀ d, HasPureCodimension
    (geometricSupport α ∩
      (pullback.fst X.hom Y.hom).base ⁻¹' (Xd d : Set X.left)) d

/-- The degree-zero correspondence predicate is specified by pure codimension of the sliced
geometric support. -/
theorem isDegreeZeroCorrespondence_iff
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    (Xd : ℕ → X.left.Opens)
    (α : AlgebraicCycle (pullback X.hom Y.hom) ℤ) :
    IsDegreeZeroCorrespondence Xd α ↔
      ∀ d, HasPureCodimension
        (geometricSupport α ∩
          (pullback.fst X.hom Y.hom).base ⁻¹' (Xd d : Set X.left)) d := sorry

/-- The graph cycle of a smooth projective morphism is a degree-zero correspondence for a
clopen equidimensional decomposition of its target. -/
theorem graph_isDegreeZeroCorrespondence
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (Xd : ℕ → X.left.Opens) (hcover : iSup Xd = ⊤)
    (hdisjoint : Pairwise (fun d e ↦ Disjoint (Xd d : Set X.left) (Xd e : Set X.left)))
    (hclopen : ∀ d, IsClopen (Xd d : Set X.left))
    (hequidimensional : ∀ d, EquidimensionalSpace (Xd d))
    (hdimension : ∀ d, (Xd d : Set X.left).Nonempty →
      topologicalKrullDim (Xd d) = (d : WithBot ℕ∞))
    (f : Y ⟶ X) :
    IsDegreeZeroCorrespondence Xd (graph f) := sorry

end AlgebraicGeometry.AlgebraicCycle
