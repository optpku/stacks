module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Intersection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 43.19.4 (1): if two coherent sheaves on a nonsingular variety have
support dimensions at most `r` and `s`, and their common support has dimension
at most `r + s - X.dimension`, then their degree-`r` and degree-`s` associated
cycles intersect properly. -/
@[stacks 0B0W] #check
  (AlgebraicGeometry.SchemeOverField.associatedCycles_intersectProperly :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.SchemeOverField k) [Variety X] [Scheme.Regular X.left]
      (F G : X.left.Modules) [F.IsCoherent] [G.IsCoherent] (r s : ℤ)
      (hF : ∀ x ∈ RingedSpace.moduleSupport F,
        X.hom.relativeDimensionFunction (fun _ ↦ 0) x ≤ r)
      (hG : ∀ x ∈ RingedSpace.moduleSupport G,
        X.hom.relativeDimensionFunction (fun _ ↦ 0) x ≤ s)
      (hFG : ∀ x ∈ RingedSpace.moduleSupport F ∩ RingedSpace.moduleSupport G,
        X.hom.relativeDimensionFunction (fun _ ↦ 0) x ≤
          r + s - (X.dimension : ℤ)),
      AlgebraicCycle.IntersectProperly
        (F.associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
        (G.associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s))

/- Lemma 43.19.4 (2): under the same support-dimension hypotheses, the
intersection of the associated cycles is the alternating sum of the associated
cycles of the Tor sheaves in degree `r + s - X.dimension`. -/
@[stacks 0B0W] #check
  (AlgebraicGeometry.SchemeOverField.intersection_associatedCycle_eq_finsum_tor :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.SchemeOverField k) [Variety X] [Scheme.Regular X.left]
      (F G : X.left.Modules) [F.IsCoherent] [G.IsCoherent] (r s : ℤ)
      [RingedSpace.ModuleDerived.Tensor.Has X.left.toRingedSpace]
      (hF : ∀ x ∈ RingedSpace.moduleSupport F,
        X.hom.relativeDimensionFunction (fun _ ↦ 0) x ≤ r)
      (hG : ∀ x ∈ RingedSpace.moduleSupport G,
        X.hom.relativeDimensionFunction (fun _ ↦ 0) x ≤ s)
      (hFG : ∀ x ∈ RingedSpace.moduleSupport F ∩ RingedSpace.moduleSupport G,
        X.hom.relativeDimensionFunction (fun _ ↦ 0) x ≤
          r + s - (X.dimension : ℤ)),
      AlgebraicCycle.intersection
          (F.associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
          (G.associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
          (AlgebraicGeometry.SchemeOverField.associatedCycles_intersectProperly
            X F G r s hF hG hFG) =
        ∑ᶠ p : ℕ, (Int.negOnePow p : ℤ) •
          Scheme.Modules.associatedCycle (RingedSpace.ModuleDerived.tor p F G)
            (X.hom.relativeDimensionFunction (fun _ ↦ 0))
            (r + s - (X.dimension : ℤ)))
