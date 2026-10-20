module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Basic

/-!
# Finite locally free morphisms of algebraic spaces

A morphism of algebraic spaces is finite locally free when it is affine and the
direct image of its structure sheaf is a finite locally free module on the
target. Rank (also called degree) is the constant-rank refinement of that
module condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite locally free morphism `f : X ⟶ Y` of algebraic spaces over `S` has
rank or degree `d` if `f_* 𝒪_X` is finite locally free of rank `d`. -/
class FiniteLocallyFreeOfRank {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) : Prop extends FiniteLocallyFree f where
  /-- The pushforward structure sheaf has rank `d`. -/
  pushforward_isFiniteLocallyFreeOfRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank d
      (Modules.pushforwardStructureModule f)

/-- The direct image of the structure module along a finite locally free
morphism of rank `d` is finite locally free of rank `d`. -/
instance FiniteLocallyFreeOfRank.module_isFiniteLocallyFreeOfRank {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ) [h : FiniteLocallyFreeOfRank f d] :
    SheafOfModules.IsFiniteLocallyFreeOfRank d
      (Modules.pushforwardStructureModule f) :=
  h.pushforward_isFiniteLocallyFreeOfRank

/-- A morphism of algebraic spaces is finite locally free of rank `d` if and
only if it is finite locally free and its pushforward structure sheaf has rank
`d`. -/
theorem finiteLocallyFreeOfRank_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) :
    FiniteLocallyFreeOfRank f d ↔
      FiniteLocallyFree f ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank d
          (Modules.pushforwardStructureModule f) :=
  sorry

namespace FiniteLocallyFreeOfRank

/-- The identity morphism of an algebraic space is finite locally free of rank
`1`. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    FiniteLocallyFreeOfRank (𝟙 X) 1 :=
  sorry

/-- The pushforward structure sheaf of a finite locally free morphism of rank
`d` is finite locally free of rank `d`. -/
@[reducible] def pushforwardStructureModule {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) [h : FiniteLocallyFreeOfRank f d] :
    SheafOfModules.IsFiniteLocallyFreeOfRank d
      (Modules.pushforwardStructureModule f) :=
  h.pushforward_isFiniteLocallyFreeOfRank

/-- A finite locally free morphism of rank `d` is finite locally free and has
pushforward structure sheaf of rank `d`. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ)
    [FiniteLocallyFreeOfRank f d] :
    FiniteLocallyFree f ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank d
        (Modules.pushforwardStructureModule f) :=
  sorry

end FiniteLocallyFreeOfRank

end AlgebraicGeometry.AlgebraicSpace
