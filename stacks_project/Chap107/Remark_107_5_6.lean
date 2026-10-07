module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Topology.Defs.Filter
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap94.Definition_94_12_2_DeligneMumford
public import stacks_project.Chap94.Lemma_94_19_1_Localization
public import stacks_project.Chap100.Definition_100_12_3_Dimension
public import stacks_project.Chap100.Example_100_12_5_Quotient
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap107.Remark_107_5_6_Scaling

/-!
# Dimension of Deligne–Mumford stacks versus the space of points

On quasi-separated locally Noetherian Deligne–Mumford stacks, stacky dimension at a
point agrees with the topological Krull dimension of `|X|`. This fails for general
Artin stacks, as shown by `[𝔸¹ / 𝔾ₘ]` and `[Spec k / 𝔾ₘ]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicStack AffineSpace
open FiberedCategoryOver.Groupoids
open scoped AlgebraicGeometry Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Absolute quasi-separatedness of an algebraic stack: after viewing over
`Spec ℤ`, the diagonal is quasi-compact and quasi-separated. This is the
source's "suitably decent (e.g. quasi-separated)" hypothesis. -/
@[mk_iff]
class IsAbsolutelyQuasiSeparated {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop where
  /-- The absolute diagonal is quasi-compact on every scheme-slice representing morphism. -/
  quasiCompact_diagonal :
    Groupoids.Hom.has
      (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
        (viewedOver (specULiftZIsTerminal.from S) X))
  /-- The absolute diagonal is quasi-separated on every scheme-slice representing morphism. -/
  quasiSeparated_diagonal :
    Groupoids.Hom.has
      (@AlgebraicSpace.QuasiSeparated (Spec (.of (ULift.{u} ℤ))))
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
        (viewedOver (specULiftZIsTerminal.from S) X))

/-- The canonical slice of a quasi-separated scheme is absolutely quasi-separated. -/
instance instIsAbsolutelyQuasiSeparated_slice {S : Scheme.{u}} (U : Over S)
    [QuasiSeparatedSpace U.left] :
    IsAbsolutelyQuasiSeparated (GroupoidsOver.slice U) :=
  sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.DeligneMumfordStack

open AlgebraicStack

/-- Remark 107.5.6 (1): for a locally Noetherian Deligne–Mumford stack which is
suitably decent (e.g. quasi-separated), the stacky dimension `dimensionAt x`
coincides with the topological local Krull dimension of `|X|` at `x`. -/
@[stacks 0DRK]
theorem dimensionAt_eq_topologicalKrullDimAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [DeligneMumfordStack X] [AlgebraicStack.IsLocallyNoetherian X]
    [IsAbsolutelyQuasiSeparated X]
    (τ : TopologicalSpace (Points X)) (hτ : IsPointsTopology X τ) (x : Points X) :
    dimensionAt x = dimensionToEInt (@topologicalKrullDimAt (Points X) τ x) :=
  sorry

end AlgebraicGeometry.DeligneMumfordStack

namespace AlgebraicGeometry.AlgebraicStack.AffineLineQuotient

/-- The two `𝔾ₘ`-orbits on `𝔸¹`, as points of `[𝔸¹ / 𝔾ₘ]`. -/
def pointsEmbedding (k : Type u) [Field k] :
    Fin 2 ↪ Points (affineLineQuotient k) where
  toFun i := if i = 0 then genericPoint k else closedPoint k
  inj' := sorry

/-- The points space of `[𝔸¹ / 𝔾ₘ]` is finite, with elements the two orbit points. -/
instance instFintype_points (k : Type u) [Field k] :
    Fintype (Points (affineLineQuotient k)) where
  elems := Finset.map (pointsEmbedding k) Finset.univ
  complete := sorry

/-- Remark 107.5.6 (2): the points space of `[𝔸¹ / 𝔾ₘ]` has two points,
corresponding to the two orbits of `𝔾ₘ` on `𝔸¹`. -/
@[stacks 0DRK]
theorem card_points (k : Type u) [Field k] :
    Fintype.card (Points (affineLineQuotient k)) = 2 :=
  sorry

/-- Remark 107.5.6 (3): the generic orbit point of `[𝔸¹ / 𝔾ₘ]` specializes to the
closed orbit point. -/
@[stacks 0DRK]
theorem specializes (k : Type u) [Field k]
    (τ : TopologicalSpace (Points (affineLineQuotient k)))
    (hτ : IsPointsTopology (affineLineQuotient k) τ) :
    @Specializes (Points (affineLineQuotient k)) τ (genericPoint k) (closedPoint k) :=
  sorry

/-- Remark 107.5.6 (4): the underlying topological space of `[𝔸¹ / 𝔾ₘ]` has
Krull dimension `1`. -/
@[stacks 0DRK]
theorem topologicalKrullDim_eq_one (k : Type u) [Field k]
    (τ : TopologicalSpace (Points (affineLineQuotient k)))
    (hτ : IsPointsTopology (affineLineQuotient k) τ) :
    @topologicalKrullDim (Points (affineLineQuotient k)) τ = (1 : WithBot ℕ∞) :=
  sorry

/-- Remark 107.5.6 (5): the stacky dimension of `[𝔸¹ / 𝔾ₘ]` is `0` at every point. -/
@[stacks 0DRK]
theorem dimensionAt_eq_zero (k : Type u) [Field k]
    (x : Points (affineLineQuotient k)) : dimensionAt x = (0 : EInt) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.AffineLineQuotient

namespace AlgebraicGeometry.AlgebraicStack

open GroupoidAlgebraicSpace GroupoidScheme

/-- The classifying stack of `𝔾ₘ` over a field is an algebraic stack. -/
instance instAlgebraicStack_classifying_multiplicativeGroup (k : Type u) [Field k] :
    AlgebraicStack (classifying (𝔾ₘ[Spec (.of k)]).toGrp) :=
  instAlgebraicStack_classifying (𝔾ₘ[Spec (.of k)]).toGrp

/-- The classifying stack of `𝔾ₘ` over a field is locally Noetherian. -/
instance instIsLocallyNoetherian_classifying_multiplicativeGroup (k : Type u)
    [Field k] : IsLocallyNoetherian (classifying (𝔾ₘ[Spec (.of k)]).toGrp) :=
  instIsLocallyNoetherian_classifying (𝔾ₘ[Spec (.of k)]).toGrp

/-- The unique point of `[Spec k / 𝔾ₘ]`, as the atlas image of the unique point of
`Spec k`. -/
def classifyingPoint_multiplicativeGroup (k : Type u) [Field k] :
    Points (classifying (𝔾ₘ[Spec (.of k)]).toGrp) :=
  Points.mapSlice
    ((AlgebraicSpace.ofOverSliceEquiv
        (Over.mk (𝟙 (Spec (.of k))))).inv ≫
      (ofGroupoidScheme
        (ofAction (𝔾ₘ[Spec (.of k)]).toGrp
          (GroupScheme.trivialAction (𝔾ₘ[Spec (.of k)]).toGrp))).atlas)
    (default : Spec (.of k))

/-- Remark 107.5.6 (6): the classifying stack `[Spec k / 𝔾ₘ]` has a unique point. -/
@[stacks 0DRK, instance]
instance instUnique_points_classifying_multiplicativeGroup (k : Type u) [Field k] :
    Unique (Points (classifying (𝔾ₘ[Spec (.of k)]).toGrp)) where
  default := classifyingPoint_multiplicativeGroup k
  uniq := sorry

/-- Remark 107.5.6 (7): the stacky dimension of `[Spec k / 𝔾ₘ]` at its unique point
is `-1`. -/
@[stacks 0DRK]
theorem dimensionAt_classifying_multiplicativeGroup (k : Type u) [Field k]
    (x : Points (classifying (𝔾ₘ[Spec (.of k)]).toGrp)) :
    dimensionAt x = ((-1 : ℤ) : EInt) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
