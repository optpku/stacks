module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field
public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap70.Lemma_70_5_4_PointClosure
public import stacks_project.Chap72.Lemma_72_14_3_GlobalSections
public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension
public import stacks_project.Chap82.Lemma_82_7_1_IntegralImage
public import stacks_project.Chap82.Lemma_82_8_2_Pushforward

/-!
# Degree of zero-cycles on proper algebraic spaces over a field

The degree of a `0`-cycle on a proper algebraic space over a field is the
coefficient of the unique point of `Spec k` after proper pushforward along the
structure morphism. On generators this recovers `dim_k Γ(Z, 𝒪_Z)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- `Spec k`, viewed as an algebraic space over itself, is universally catenary. -/
instance instUniversallyCatenary_specField (k : Type u) [Field k] :
    UniversallyCatenary (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :=
  sorry

/-- `Spec k`, viewed as an algebraic space over itself, is quasi-separated. -/
instance instIsQuasiSeparated_specField (k : Type u) [Field k] :
    IsQuasiSeparated (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :=
  sorry

/-- The spectrum of a field has a unique point. -/
instance instUnique_specOfField (k : Type u) [Field k] :
    Unique (Spec (CommRingCat.of k)) :=
  inferInstanceAs (Unique (PrimeSpectrum k))

/-- The unique scheme-theoretic point of `Spec k`, as the source of the identity
over-map. -/
def specFieldSchemePoint (k : Type u) [Field k] :
    (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
  (default : Spec (CommRingCat.of k))

/-- `specFieldSchemePoint k` is the unique point of `Spec k`. -/
theorem specFieldSchemePoint_eq (k : Type u) [Field k] :
    specFieldSchemePoint k = (default : Spec (CommRingCat.of k)) :=
  sorry

/-- The points of `Spec k` as an algebraic space form a `T₁` space. -/
instance instT1Space_points_specField (k : Type u) [Field k] :
    T1Space (Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :=
  sorry

/-- The constant-zero function is a dimension function on the points of `Spec k`. -/
instance instIsDimensionFunction_zero_specField (k : Type u) [Field k] :
    IsDimensionFunction
      (fun _ : Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))) ↦ (0 : ℤ)) :=
  inferInstance

/-- The structure morphism of `Spec k` as an algebraic space over itself is proper. -/
instance instProper_toBase_specField (k : Type u) [Field k] :
    Proper (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :=
  sorry

/-- Reduced closures of points of a proper algebraic space over a field remain proper
over `k`. -/
instance instProper_toBase_pointClosure {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)] (x : Points X) :
    Proper (toBase (PointClosure.space x)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The unique point of `Spec k` as an algebraic space over itself. -/
def specFieldPoint (k : Type u) [Field k] :
    Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :=
  ofOver.pointsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (specFieldSchemePoint k)

/-- Points of `Spec k` as an algebraic space are unique. -/
instance instUnique_points_specField (k : Type u) [Field k] :
    Unique (Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) where
  default := specFieldPoint k
  uniq := sorry

/-- `specFieldPoint k` is the image of the unique scheme point of `Spec k`. -/
theorem specFieldPoint_eq (k : Type u) [Field k] :
    specFieldPoint k =
      ofOver.pointsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (specFieldSchemePoint k) :=
  sorry

/-- Proper pushforward of `0`-cycles to `Spec k` is additive on coefficients at the
unique point. -/
theorem zeroCycleDegree_add {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)]
    (α β : (toBase X).cycleGroup (fun _ ↦ (0 : ℤ)) 0) :
    properPushforwardCycle (toBase X)
        (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
        (fun _ ↦ (0 : ℤ)) (toBase X)
        (eq_toBase (toBase X ≫
          toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))))
        (α + β : Function.locallyFinsupp (Points X) ℤ) (specFieldPoint k) =
      properPushforwardCycle (toBase X)
          (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
          (fun _ ↦ (0 : ℤ)) (toBase X)
          (eq_toBase (toBase X ≫
            toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))))
          (α : Function.locallyFinsupp (Points X) ℤ) (specFieldPoint k) +
        properPushforwardCycle (toBase X)
          (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
          (fun _ ↦ (0 : ℤ)) (toBase X)
          (eq_toBase (toBase X ≫
            toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))))
          (β : Function.locallyFinsupp (Points X) ℤ) (specFieldPoint k) :=
  sorry

/-- The degree of a `0`-cycle on a proper algebraic space over a field, obtained by
proper pushforward to `Spec k` and reading the coefficient of the unique point. -/
def zeroCycleDegree {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)] :
    (toBase X).cycleGroup (fun _ ↦ (0 : ℤ)) 0 →+ ℤ :=
  AddMonoidHom.mk'
    (fun α ↦
      properPushforwardCycle (toBase X)
        (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
        (fun _ ↦ (0 : ℤ)) (toBase X)
        (eq_toBase (toBase X ≫
          toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))))
        (α : Function.locallyFinsupp (Points X) ℤ) (specFieldPoint k))
    zeroCycleDegree_add

/-- The degree of a `0`-cycle is the coefficient of the unique point of `Spec k`
after proper pushforward along the structure morphism. -/
theorem zeroCycleDegree_apply {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)]
    (α : (toBase X).cycleGroup (fun _ ↦ (0 : ℤ)) 0) :
    zeroCycleDegree α =
      properPushforwardCycle (toBase X)
        (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
        (fun _ ↦ (0 : ℤ)) (toBase X)
        (eq_toBase (toBase X ≫
          toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))))
        (α : Function.locallyFinsupp (Points X) ℤ) (specFieldPoint k) :=
  sorry

/-- The degree of a `0`-cycle is the finite sum of its coefficients weighted by
`dim_k Γ(Z_x, 𝒪_{Z_x})` of the reduced point closures. -/
theorem zeroCycleDegree_eq_finsum {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)]
    (α : (toBase X).cycleGroup (fun _ ↦ (0 : ℤ)) 0) :
    zeroCycleDegree α =
      ∑ᶠ x : Points X,
        (α : Function.locallyFinsupp (Points X) ℤ) x *
          (Module.finrank k (globalSectionsAlg (PointClosure.space x)) : ℤ) :=
  sorry

/-- The singleton cycle `[Z]` of an integral closed subspace of relative dimension
`0` is a `0`-cycle. -/
theorem mem_cycleGroup_single {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)]
    (Z : ClosedSubspace X) [IsIntegral Z.X]
    (hZ : (toBase X).closedSubspaceDeltaDimension (fun _ ↦ (0 : ℤ)) Z = (0 : EInt)) :
    @locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        (Points.map Z.ι (ClosedSubspace.integralGenericPoint Z)) 1 ∈
      (toBase X).cycleGroup (fun _ ↦ (0 : ℤ)) 0 :=
  sorry

/-- The degree of the generator `[Z]` is `dim_k Γ(Z, 𝒪_Z)`. -/
theorem zeroCycleDegree_single {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)]
    (Z : ClosedSubspace X) [IsIntegral Z.X]
    (hZ : (toBase X).closedSubspaceDeltaDimension (fun _ ↦ (0 : ℤ)) Z = (0 : EInt)) :
    zeroCycleDegree ⟨@locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        (Points.map Z.ι (ClosedSubspace.integralGenericPoint Z)) 1,
      mem_cycleGroup_single Z hZ⟩ =
      (Module.finrank k (globalSectionsAlg Z.X) : ℤ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
