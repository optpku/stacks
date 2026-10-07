module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.SingularPointSequence

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SingularPointBlowupSequence

/-- Every post-initial stage of a singular-point blowup sequence is at worst nodal over the
original base morphism. -/
def EveryTargetAtWorstNodal {X Y S : Scheme.{u}}
    (s : SingularPointBlowupSequence X Y) (f : X ⟶ S) : Prop :=
  match s with
  | .nil _ => True
  | @cons _ _ _ _ _ b _ tail =>
      AtWorstNodal (b ≫ f) ∧ tail.EveryTargetAtWorstNodal (b ≫ f)

/-- The empty singular-point blowup sequence has no post-initial nodal stages. -/
theorem everyTargetAtWorstNodal_nil {X S : Scheme.{u}} (f : X ⟶ S) :
    (nil X).EveryTargetAtWorstNodal f ↔ True := sorry

/-- The stagewise at-worst-nodal condition unfolds across the first blowup and its tail. -/
theorem everyTargetAtWorstNodal_cons {X X' Y S : Scheme.{u}}
    (p : closedPoints X) (h_singular : p.1 ∈ Sing(X)) (b : X' ⟶ X)
    (h_blowup : IsBlowup b
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)))
    (tail : SingularPointBlowupSequence X' Y) (f : X ⟶ S) :
    (cons p h_singular b h_blowup tail).EveryTargetAtWorstNodal f ↔
      AtWorstNodal (b ≫ f) ∧ tail.EveryTargetAtWorstNodal (b ≫ f) := sorry

end AlgebraicGeometry.Scheme.SingularPointBlowupSequence

namespace AlgebraicGeometry.Scheme.Hom

/-- A quasi-compact at-worst-nodal relative-dimension-one scheme over a discrete valuation
ring with smooth generic fibre admits a finite sequence of blowups at singular closed
points, preserving at-worst-nodality at every stage and ending in a regular scheme. -/
theorem exists_regular_singularPointBlowupSequence
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [AtWorstNodal f]
    [Smooth (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))] :
    ∃ (m : ℕ) (Y : Scheme.{u})
      (s : SingularPointBlowupSequence X Y),
      s.length = m ∧ Scheme.Regular Y ∧
        s.EveryTargetAtWorstNodal f := sorry

end AlgebraicGeometry.Scheme.Hom
