module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange.Limit
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.FiniteIntermediate
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Compact

/-!
# Chow groups over finite intermediate fields

For a field extension `K / k` and a finite-type `k`-scheme `X`, this module specializes the
continuity diagram and cocone of `AlgebraicGeometry.ChowLimit` to the inverse system of
spectra of finite intermediate fields `K / k' / k`, graded by the constant-zero dimension
functions. For an algebraic extension the resulting cocone is a colimit: Stacks 0FH6 is the
special case of Stacks 0FVQ.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.FieldExtension

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.FieldExtension

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
variable (X : Over (Spec (CommRingCat.of k))) [Scheme.Hom.FiniteType X.hom]
variable (i : ℤ)

/-- The directed system `k' ↦ CH_i(X_{k'})` over the finite intermediate fields `K / k' / k`,
with zero-shift flat pullbacks as transition maps. -/
abbrev finiteIntermediateChowDiagram : FiniteIntermediateField k K ⥤ AddCommGrpCat.{u} :=
  ChowLimit.chowDiagram (finiteIntermediateSpecDiagram k K) (finiteIntermediateStructure k K)
    (fun _ ↦ (0 : ℤ)) X i (fun _ _ h ↦ finiteIntermediateTransition_compatible k K h)
    (hD_catenary := finiteIntermediateDiagram_universallyCatenary k K)
    (hD_dimension := finiteIntermediateStageDimensions k K)
    (htransition_flat := finiteIntermediateTransitionMaps_flat k K)

/-- The cocone of flat pullbacks `CH_i(X_{k'}) → CH_i(X_K)` over the finite intermediate
fields `K / k' / k`. -/
abbrev finiteIntermediateChowCocone : Cocone (finiteIntermediateChowDiagram k K X i) :=
  ChowLimit.chowCocone (finiteIntermediateSpecDiagram k K) (finiteIntermediateStructure k K)
    (fun _ ↦ (0 : ℤ)) X i (fun _ _ h ↦ finiteIntermediateTransition_compatible k K h)
    (finiteIntermediateCone k K) (FieldExtension.specMap k K) (fun _ ↦ (0 : ℤ))
    (finiteIntermediateCone_compatible k K) (finiteIntermediateConeMap_compatible k K)
    (hD_catenary := finiteIntermediateDiagram_universallyCatenary k K)
    (hD_dimension := finiteIntermediateStageDimensions k K)
    (htransition_flat := finiteIntermediateTransitionMaps_flat k K)
    (hc_catenary := (inferInstance : UniversallyCatenary (Spec (CommRingCat.of K))))
    (hδ' := (inferInstance : IsDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))))
    (hleg_flat := finiteIntermediateConeMaps_flat k K)

/-- For an algebraic extension `K / k` and a finite-type `k`-scheme `X`,
`CH_i(X_K) = colim CH_i(X_{k'})` over the finite subextensions `K / k' / k`. -/
theorem finiteIntermediateChowCocone_isColimit [Algebra.IsAlgebraic k K] :
    Nonempty (IsColimit (finiteIntermediateChowCocone k K X i)) := sorry

end AlgebraicGeometry.ChowGroup.FieldExtension
