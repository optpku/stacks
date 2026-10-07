module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.Ample.Descent
import StacksCheckRecall

/-!
# Proposition 31.17.9

Descent of ample invertible modules along standard classes of finite surjections.

@stack 0BD4
-/

@[expose] public section

open CategoryTheory

universe u

/- Proposition 31.17.9 (1): finite locally free case. -/
@[stacks 0BD4] #check
  (AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule.target_of_isFiniteLocallyFree_surjective :
    {X Y : AlgebraicGeometry.Scheme.{u}} → (π : X ⟶ Y) →
      [AlgebraicGeometry.IsFiniteLocallyFree π] → [AlgebraicGeometry.Surjective π] →
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X →
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule Y)

/- Proposition 31.17.9 (2): integral normal target case. -/
@[stacks 0BD4] #check
  (AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule.target_of_isFinite_surjective_isIntegral_isNormal :
    {X Y : AlgebraicGeometry.Scheme.{u}} → (π : X ⟶ Y) →
      [AlgebraicGeometry.IsFinite π] → [AlgebraicGeometry.Surjective π] →
      [AlgebraicGeometry.IsIntegral Y] → Y.isNormal →
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X →
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule Y)

/- Proposition 31.17.9 (3): prime-characteristic reduction case. -/
@[stacks 0BD4] #check
  (AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule.target_of_isFinite_surjective_isNoetherian_isCharP_isReduction :
    {X Y : AlgebraicGeometry.Scheme.{u}} → (π : X ⟶ Y) →
      [AlgebraicGeometry.IsFinite π] → [AlgebraicGeometry.Surjective π] →
      [AlgebraicGeometry.IsNoetherian Y] → (p : ℕ) → [Fact (Nat.Prime p)] →
      [AlgebraicGeometry.Scheme.IsCharP Y p] →
      (e : X ≅ AlgebraicGeometry.Scheme.reduction Y) →
      e.hom ≫ AlgebraicGeometry.Scheme.reductionι Y = π →
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X →
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule Y)
