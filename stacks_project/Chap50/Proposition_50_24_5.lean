module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.PoincareDuality.Relative
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.DeRham
open scoped AlgebraicGeometry

universe u

/- Proposition 50.24.5: existence of a relative de Rham trace with perfect cup pairing. -/
@[stacks 0G8K] #check
  (AlgebraicGeometry.Scheme.DeRham.existsRelativeDeRhamPoincareTrace :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
    [Scheme.Hom.RelativeDimension f n],
    (∀ s : S, Nonempty (f.fiber s)) →
    ∃ t : PoincareDuality.topCohomology f n ⟶ PoincareDuality.structureModule S,
      ∃ τ : (PoincareDuality.pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
          PoincareDuality.derivedStructureModule S,
        PoincareDuality.topTrace f n τ = t ∧ PoincareDuality.IsPerfect f n τ)

/- Proposition 50.24.5: uniqueness of perfect traces up to multiplication by a global unit. -/
@[stacks 0G8K] #check
  (AlgebraicGeometry.Scheme.DeRham.relativeDeRhamPoincareTrace_unique :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
    [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s))
    (t t' : PoincareDuality.topCohomology f n ⟶ PoincareDuality.structureModule S)
    (τ τ' : (PoincareDuality.pushforward f)⟦(2 * (n : ℤ))⟧ ⟶
      PoincareDuality.derivedStructureModule S),
    PoincareDuality.topTrace f n τ = t →
    PoincareDuality.topTrace f n τ' = t' →
    PoincareDuality.IsPerfect f n τ →
    PoincareDuality.IsPerfect f n τ' →
    ∃ a : Γ(X, ⊤)ˣ,
      t' = PoincareDuality.unitAction f n h_nonempty a ≫ t)
