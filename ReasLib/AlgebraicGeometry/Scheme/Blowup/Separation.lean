module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import Mathlib.Topology.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Blowup

/-!
# Separating open subschemes by admissible blowups

This file records a separation result for disjoint quasi-compact open subschemes using an
admissible blowup.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- Two disjoint quasi-compact open subschemes of a quasi-compact quasi-separated scheme have
disjoint inverse images contained in a two-open cover after an admissible blowup. -/
theorem exists_isAdmissibleBlowup_disjointOpenCover_of_disjoint_qc_opens
    {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (U V : X.Opens) (hU : QuasiCompact U.ι) (hV : QuasiCompact V.ι)
    (hUV : Disjoint (U : Set X) (V : Set X)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
      IsAdmissibleBlowup (U ⊔ V) b ∧
        ∃ X₁ X₂ : X'.Opens,
          Disjoint (X₁ : Set X') (X₂ : Set X') ∧
            X₁ ⊔ X₂ = ⊤ ∧
              (b ⁻¹ᵁ U) ≤ X₁ ∧
                (b ⁻¹ᵁ V) ≤ X₂ := sorry

/-- Two finitely presented closed subschemes that do not meet over a quasi-compact open have
disjoint strict transforms after an admissible blowup. -/
theorem exists_isAdmissibleBlowup_disjointStrictTransforms
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) [QuasiCompact U.ι]
    (Z₁ Z₂ : X.IdealSheafData)
    [Scheme.Hom.FinitePresentation Z₁.subschemeι]
    [Scheme.Hom.FinitePresentation Z₂.subschemeι]
    (h : Disjoint ((Z₁.support : Set X) ∩ (Z₂.support : Set X)) (U : Set X)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X) (I : X.IdealSheafData),
      IsAdmissibleBlowupCenter U b I ∧
        Disjoint
          (Set.range (strictTransformSnd b (I.comap b) Z₁.subschemeι).base)
          (Set.range (strictTransformSnd b (I.comap b) Z₂.subschemeι).base) := sorry

/-- Two disjoint constructible closed subsets of a quasi-compact open have disjoint closures
after an admissible blowup. -/
theorem exists_isAdmissibleBlowup_disjointConstructibleClosures
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) [QuasiCompact U.ι]
    (T₁ T₂ : TopologicalSpace.Closeds U)
    (hT₁ : Topology.IsConstructible (T₁ : Set U))
    (hT₂ : Topology.IsConstructible (T₂ : Set U))
    (h : Disjoint T₁ T₂) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
      IsAdmissibleBlowup U b ∧
        Disjoint
          (closure (b.base ⁻¹' Set.image U.ι.base (T₁ : Set U)))
          (closure (b.base ⁻¹' Set.image U.ι.base (T₂ : Set U))) := sorry

end AlgebraicGeometry
