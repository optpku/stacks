/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Noetherian.ULift
public import stacks_project.Chap66.Lemma_66_33_1_Affine
public import stacks_project.Chap99.Lemma_99_15_10_Versal

/-!
# Lemma 99.15.10

The stack in groupoids `𝒳 = Curves` satisfies openness of versality over
`specZ`. After the base change of Remark 99.15.5, the same axiom holds over
any Noetherian base scheme `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- `specZ` is a Noetherian scheme. -/
instance instIsNoetherian_specZ : AlgebraicGeometry.IsNoetherian specZ :=
  inferInstance

/-- Lemma 99.15.10 (1): the stack in groupoids `𝒳 = Curves` satisfies openness
of versality over `specZ`. If `U ⟶ specZ` is locally of finite type, `x` is an
object of `𝒳` over `U`, and `u0 ∈ U` is a finite type point at which `x` is
versal, then there is an open neighbourhood `u0 ∈ U' ⊂ U` such that `x` is
versal at every finite type point of `U'`. -/
@[stacks 0D59]
theorem opennessOfVersality_specZ {U : Scheme.{u}} (hU : U ⟶ specZ)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj specZ)
    (hx : (p specZ).obj x = Over.mk hU) (u0 : U) :
    IsFiniteTypePoint u0 → IsVersalAt hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u :=
  sorry

/-- Lemma 99.15.10 (2): after base change (Remark 99.15.5), openness of
versality holds over any Noetherian base scheme `S`. If `U ⟶ S` is locally of
finite type, `x` is an object of `𝒳 = Curves` over `U`, and `u0 ∈ U` is a
finite type point at which `x` is versal, then there is an open neighbourhood
`u0 ∈ U' ⊂ U` such that `x` is versal at every finite type point of `U'`. -/
@[stacks 0D59]
theorem opennessOfVersality {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {U : Scheme.{u}}
    (hU : U ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj S)
    (hx : (p S).obj x = Over.mk hU) (u0 : U) :
    IsFiniteTypePoint u0 → IsVersalAt hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u :=
  sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
