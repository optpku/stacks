/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Point

/-!
# Local fibre dimensions under base change

This leaf records local-ring dimension and residue-field transcendence-degree
formulas for a pullback square of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiberDimension

/-- In a pullback square, the dimension of the local ring of the fibre of the
induced map between fixed fibres, added to the original fixed-fibre stalk
dimension, is the pullback fixed-fibre stalk dimension. -/
theorem ringKrullDim_baseChangeFiberStalkAt_add_eq_of_isPullback
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') :
    ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') +
        ringKrullDim (fiberStalkAt f (g' x')) =
      ringKrullDim (fiberStalkAt f' x') := sorry

/-- In a pullback square, the dimension of the local ring of the fibre of the
induced map between fixed fibres is the difference of the two fixed-fibre
stalk dimensions. -/
theorem ringKrullDim_baseChangeFiberStalkAt_eq_sub_of_isPullback
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') :
    ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') =
      ((ringKrullDim (fiberStalkAt f' x')).unbotD 0).toNat -
        ((ringKrullDim (fiberStalkAt f (g' x'))).unbotD 0).toNat := sorry

/-- In a pullback square, the dimension of the local ring of the fibre of the
induced fixed-fibre map, added to the upstairs residue-field transcendence
degree, is the residue-field transcendence degree at the image point. -/
theorem baseChangeFiberStalkDim_add_trdeg_eq
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') :
    ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') +
        f'.residueFieldTrdegAt x' =
      f.residueFieldTrdegAt (g' x') := sorry

/-- In a pullback square, the dimension of the local ring of the fibre of the
induced fixed-fibre map is the difference of the corresponding residue-field
transcendence degrees. -/
theorem baseChangeFiberStalkDim_eq_trdeg_sub
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') :
    ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') =
      f.residueFieldTrdegAt (g' x') - f'.residueFieldTrdegAt x' := sorry

/-- Pullback does not decrease the Krull dimension of the local ring at the
distinguished point of a fixed scheme-theoretic fibre. -/
theorem ringKrullDim_fiberStalkAt_le_of_isPullback
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') :
    ringKrullDim (fiberStalkAt f (g' x')) ≤ ringKrullDim (fiberStalkAt f' x') := sorry

/-- The residue-field transcendence degree at a point of a pullback is at
most that at its image in the original scheme. -/
theorem residueFieldTrdegAt_le_of_isPullback
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') :
    f'.residueFieldTrdegAt x' ≤ f.residueFieldTrdegAt (g' x') := sorry

/-- Given compatible points of the base and the original scheme in a
pullback square, there is a point above both for which the fixed-fibre stalk
dimensions and residue-field transcendence degrees are preserved. -/
theorem exists_point_fiberStalkDim_eq_and_residueFieldTrdegAt_eq_of_isPullback
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (s' : S') (x : X) (hxs : f x = g s') :
    ∃ x' : X',
      g' x' = x ∧
        f' x' = s' ∧
        ringKrullDim (fiberStalkAt f' x') = ringKrullDim (fiberStalkAt f x) ∧
        f'.residueFieldTrdegAt x' = f.residueFieldTrdegAt x := sorry

/-- Under a surjective base change of a locally finite type morphism, every
point lifts to a point with the same residue-field transcendence degree. -/
theorem exists_point_residueFieldTrdegAt_eq_of_isPullback_of_surjective
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) [Surjective g] (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (r : ℕ) (x : X)
    (hx : f.residueFieldTrdegAt x = r) :
    ∃ x' : X', g' x' = x ∧ f'.residueFieldTrdegAt x' = r := sorry

/-- Two lifts of a point under a surjective base change of a locally finite
type morphism, both preserving its residue-field transcendence degree, admit
a common lift of the same degree over the double base change, whose projections
are compatible over the original scheme. -/
theorem exists_point_residueFieldTrdegAt_eq_of_doublePullback
    {S X S' X' S'' X'' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) [Surjective g] (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hX' : IsPullback g' f' f g) (pr₁ pr₂ : S'' ⟶ S')
    (hS'' : IsPullback pr₁ pr₂ g g) (p₁ p₂ : X'' ⟶ X') (f'' : X'' ⟶ S'')
    (h₁ : IsPullback p₁ f'' f' pr₁) (h₂ : IsPullback p₂ f'' f' pr₂)
    (hprojection : p₁ ≫ g' = p₂ ≫ g')
    (r : ℕ) (x : X) (hx : f.residueFieldTrdegAt x = r)
    (x₁ x₂ : X') (hx₁ : g' x₁ = x) (hx₂ : g' x₂ = x)
    (htr₁ : f'.residueFieldTrdegAt x₁ = r)
    (htr₂ : f'.residueFieldTrdegAt x₂ = r) :
    ∃ x'' : X'',
      p₁ x'' = x₁ ∧ p₂ x'' = x₂ ∧ f''.residueFieldTrdegAt x'' = r := sorry

end AlgebraicGeometry.Scheme.Hom.FiberDimension
