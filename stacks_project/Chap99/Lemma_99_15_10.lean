/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OpennessOfVersality
import StacksCheckRecall

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

/- Lemma 99.15.10: openness of versality for families of curves over every
Noetherian base scheme. -/
@[stacks 0D59]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.opennessOfVersality :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {U : Scheme.{u}}
    (hU : U ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Curves.Obj S)
    (hx : (Curves.p S).obj x = Over.mk hU) (u0 : U),
    IsFiniteTypePoint u0 → Curves.IsVersalAt hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → Curves.IsVersalAt hU x hx u)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.opennessOfVersality_specZ :
  ∀ {U : Scheme.{u}} (hU : U ⟶ specZ)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Curves.Obj specZ)
    (hx : (Curves.p specZ).obj x = Over.mk hU) (u0 : U),
    IsFiniteTypePoint u0 → Curves.IsVersalAt hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → Curves.IsVersalAt hU x hx u)
