module

public import stacks_project.Chap68.Definition_68_3_1_FiberDegree

/-!
# Base change of universally bounded fibres

Universally bounded fibres of a morphism from a scheme to an algebraic space are
preserved by base change along a representable morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.3.3: Let `S` be a scheme. Let `Y ⟶ X` be a representable morphism of
algebraic spaces over `S`. Let `U ⟶ X` be a morphism from a scheme to `X`. If the
fibres of `U ⟶ X` are universally bounded, then the fibres of `U ×_X Y ⟶ Y` are
universally bounded.

Representability of `g : Y ⟶ X` makes the represented pullback `hg.pullback f` a
scheme over `S`, so the definition applies to
`hg.fst f : ofOver (hg.pullback f) ⟶ Y`. -/
@[stacks 03JN]
theorem universallyBoundedFibres_baseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {U : Over S} (g : Y ⟶ X) (hg : yoneda.relativelyRepresentable g)
    (f : ofOver U ⟶ X) (hf : universallyBoundedFibres f) :
    universallyBoundedFibres (hg.fst f) :=
  sorry

/-- A fixed numerical bound on fibre degrees is preserved by represented base change. -/
theorem degreesOfFibresBoundedBy_baseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {U : Over S} (g : Y ⟶ X) (hg : yoneda.relativelyRepresentable g)
    (f : ofOver U ⟶ X) {n : ℕ} (hf : degreesOfFibresBoundedBy f n) :
    degreesOfFibresBoundedBy (hg.fst f) n :=
  sorry

/-- Universal fibre boundedness is preserved along an arbitrary represented pullback
square in `AlgebraicSpace S`. -/
theorem universallyBoundedFibres_of_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {U P : Over S} {g : Y ⟶ X} {f : ofOver U ⟶ X} {πY : ofOver P ⟶ Y}
    {πU : ofOver P ⟶ ofOver U} (sq : IsPullback πY πU g f)
    (hf : universallyBoundedFibres f) : universallyBoundedFibres πY :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
