module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_30_1_Separation
public import stacks_project.Chap88.Definition_88_20_1
public import stacks_project.Chap88.Definition_88_21_1

/-!
# Rig-surjectivity with a rig-étale, rig-surjective diagonal

A locally of finite type morphism of locally Noetherian formal algebraic
spaces whose relative diagonal is both rig-étale and rig-surjective is
rig-surjective if and only if every adic test map from the formal spectrum
of a complete discrete valuation ring lifts through the source, with no
extension of discrete valuation rings required.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective

/-- Lemma 88.22.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces. Assume `X` and `Y` are locally Noetherian, `f` is
locally of finite type, and the relative diagonal
`diagonal f : X ⟶ pullback f f` is rig-étale and rig-surjective. Then `f`
is rig-surjective if and only if every adic morphism `Spf(R) ⟶ Y` from a
complete discrete valuation ring `R` lifts to a morphism `Spf(R) ⟶ X`. -/
@[stacks 0GDA]
theorem iff_adicSpf_lifts {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [HasPullback f f]
    [IsFormalAlgebraicSpace (pullback f f)] [IsLocallyNoetherian (pullback f f)]
    [LocallyOfFiniteType (diagonal f)] [RigEtale (diagonal f)]
    [RigSurjective (diagonal f)] :
    RigSurjective f ↔
      ∀ sq : AdicSpfSquare f, ∃ lift : sq.specSpf ⟶ X, lift ≫ f = sq.p :=
  sorry

/-- A locally of finite type morphism of locally Noetherian formal algebraic
spaces whose relative diagonal is both rig-étale and rig-surjective, if
itself rig-surjective, admits an on-the-nose lift of every adic test map
`Spf(R) ⟶ Y` from a complete discrete valuation ring through the source. -/
theorem exists_lift {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [HasPullback f f]
    [IsFormalAlgebraicSpace (pullback f f)] [IsLocallyNoetherian (pullback f f)]
    [LocallyOfFiniteType (diagonal f)] [RigEtale (diagonal f)]
    [RigSurjective (diagonal f)] [RigSurjective f]
    (sq : AdicSpfSquare f) :
    ∃ lift : sq.specSpf ⟶ X, lift ≫ f = sq.p :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective
