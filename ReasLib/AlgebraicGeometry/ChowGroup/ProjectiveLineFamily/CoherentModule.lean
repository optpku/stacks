/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineFamily.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveLineFamily.Module

/-!
# Endpoint cycles of coherent modules on projective-line families

This file defines the associated cycles of the restrictions of a coherent module to the
zero and infinity sections of `X ×ₛ ℙ¹ₛ` and states their rational equivalence under support
dimension and embedded-point hypotheses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineFamily

/-- The degree-`k` associated cycle of the zero restriction of a coherent family. -/
noncomputable def zeroAssociatedCycle {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta] (X : Over S)
    [LocallyOfFiniteType X.hom] (F : (space X).Modules) [F.IsCoherent] (k : ℤ) :
    CycleGroup X.left (X.hom.relativeDimensionFunction delta) k :=
  let hX := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let hSpace := LocallyOfFiniteType.isLocallyNoetherian (toBase X)
  let hF := @Scheme.Modules.pullback_isCoherent X.left (space X) hX hSpace
    (zeroSection X) F inferInstance
  ⟨@Scheme.Modules.associatedCycle X.left hX (zeroRestriction X F) hF
      (X.hom.relativeDimensionFunction delta) k,
    @Scheme.Modules.associatedCycle_mem_dimensionSubgroup X.left hX (zeroRestriction X F) hF
      (X.hom.relativeDimensionFunction delta) k⟩

/-- The underlying algebraic cycle of `zeroAssociatedCycle` is the associated cycle of the
zero restriction. -/
theorem zeroAssociatedCycle_toAlgebraicCycle {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta] (X : Over S)
    [LocallyOfFiniteType X.hom] (F : (space X).Modules) [F.IsCoherent] (k : ℤ) :
    CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction delta) k
        (zeroAssociatedCycle delta X F k) =
      @Scheme.Modules.associatedCycle X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom) (zeroRestriction X F)
        (@Scheme.Modules.pullback_isCoherent X.left (space X)
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (LocallyOfFiniteType.isLocallyNoetherian (toBase X))
          (zeroSection X) F inferInstance)
        (X.hom.relativeDimensionFunction delta) k := sorry

/-- The degree-`k` associated cycle of the infinity restriction of a coherent family. -/
noncomputable def infinityAssociatedCycle {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta] (X : Over S)
    [LocallyOfFiniteType X.hom] (F : (space X).Modules) [F.IsCoherent] (k : ℤ) :
    CycleGroup X.left (X.hom.relativeDimensionFunction delta) k :=
  let hX := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let hSpace := LocallyOfFiniteType.isLocallyNoetherian (toBase X)
  let hF := @Scheme.Modules.pullback_isCoherent X.left (space X) hX hSpace
    (infinitySection X) F inferInstance
  ⟨@Scheme.Modules.associatedCycle X.left hX (infinityRestriction X F) hF
      (X.hom.relativeDimensionFunction delta) k,
    @Scheme.Modules.associatedCycle_mem_dimensionSubgroup X.left hX
      (infinityRestriction X F) hF (X.hom.relativeDimensionFunction delta) k⟩

/-- The underlying algebraic cycle of `infinityAssociatedCycle` is the associated cycle of the
infinity restriction. -/
theorem infinityAssociatedCycle_toAlgebraicCycle
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom]
    (F : (space X).Modules) [F.IsCoherent] (k : ℤ) :
    CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction delta) k
        (infinityAssociatedCycle delta X F k) =
      @Scheme.Modules.associatedCycle X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom) (infinityRestriction X F)
        (@Scheme.Modules.pullback_isCoherent X.left (space X)
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (LocallyOfFiniteType.isLocallyNoetherian (toBase X))
          (infinitySection X) F inferInstance)
        (X.hom.relativeDimensionFunction delta) k := sorry

/-- For a coherent module on `X ×ₛ ℙ¹ₛ` satisfying the support-dimension bounds and the
embedded-associated-point condition at the endpoints, the degree-`k` associated cycles of
its zero and infinity restrictions are rationally equivalent on `X`. -/
theorem fiberCycles_rationallyEquivalent
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom]
    (F : (space X).Modules) [F.IsCoherent] (k : ℤ)
    (h_dimension :
      (toBase X).closedSubschemeDeltaDimension delta
        (Scheme.Modules.schemeTheoreticSupport F) ≤
        ((k + 1 : ℤ) : EInt))
    (h_zero_dimension :
      X.hom.closedSubschemeDeltaDimension delta
        (Scheme.Modules.schemeTheoreticSupport (zeroRestriction X F)) ≤ (k : EInt))
    (h_infinity_dimension :
      X.hom.closedSubschemeDeltaDimension delta
        (Scheme.Modules.schemeTheoreticSupport (infinityRestriction X F)) ≤ (k : EInt))
    (h_embedded : ∀ ξ : space X, ξ ∈ F.embeddedAssociatedPoints →
      ξ ∉ (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
            (ProjectiveLine.Relative.zeroDivisor S).support ∪
          (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)).base ⁻¹'
            (ProjectiveLine.Relative.infinityDivisor S).support ∨
        (toBase X).relativeDimensionFunction delta ξ < k) :
    @RationalEquivalence.RationallyEquivalent X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction delta) inferInstance k
      (zeroAssociatedCycle delta X F k) (infinityAssociatedCycle delta X F k) := sorry

end AlgebraicGeometry.ProjectiveLineFamily
