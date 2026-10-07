module

public import stacks_project.Chap67.Lemma_67_15_2
public import stacks_project.Chap75.Lemma_75_7_4_Preimage

/-!
# Closed support of modules on algebraic spaces

The closed support of an `𝒪_X`-module is the topological closure of its
étale-site support. For a finite-type quasi-coherent module this coincides
with the support itself, and properness of closed support over a base is
preserved by pullback in a cartesian square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The closed support of an `𝒪_X`-module is the topological closure of its
étale-site support. -/
def closedSupport {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    Closeds (Points X) :=
  Closeds.closure (moduleSupport F)

/-- For a finite-type quasi-coherent `𝒪_X`-module, the closed support is the
étale-site support. -/
@[simp]
theorem coe_closedSupport {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] :
    (closedSupport F : Set (Points X)) = moduleSupport F :=
  sorry

/-- Pullback of a finite-type quasi-coherent `𝒪_X`-module carries closed support
to inverse image along the induced map on points. -/
theorem closedSupport_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (f : Y ⟶ X) :
    closedSupport ((pullback f).obj F) =
      (closedSupport F).preimage (Points.continuous_map f) :=
  sorry

/-- In a cartesian square of algebraic spaces, pullback preserves properness over
the base of the closed support of a finite-type quasi-coherent module. -/
theorem closedSupport_pullback_isProperOver {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    [ClosedSubset.IsProperOver f (closedSupport F)] :
    ClosedSubset.IsProperOver f' (closedSupport ((pullback g').obj F)) :=
  sorry

/-- Properness of closed support over a base is preserved by inverse image along
the source projection of a chosen pullback. -/
theorem closedSupport_pullback_isProperOver_snd {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    [ClosedSubset.IsProperOver f (closedSupport F)] :
    ClosedSubset.IsProperOver (Limits.pullback.snd f g)
      (closedSupport ((pullback (Limits.pullback.fst f g)).obj F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
