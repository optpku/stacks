/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_28_4_QCoh
public import stacks_project.Chap85.Lemma_85_28_4_Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 85.28.4

If `f : X ⟶ S` is a morphism of schemes with a section and `(X/S)_•` is the
Čech nerve of `f`, then pullback is an equivalence between quasi-coherent
`𝒪_S`-modules and quasi-coherent modules on `((X/S)_•)_Zar`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SimplicialObject

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- Lemma 85.28.4: let `f : X ⟶ S` be a morphism of schemes which has a section.
Let `(X/S)_•` be the simplicial scheme `f.simplicialScheme` associated to
`X ⟶ S`. Then `QCoh.pullback f` is an equivalence between the category
`Scheme.QCoh S` of quasi-coherent `𝒪_S`-modules and the category
`QCoh f.simplicialScheme` of quasi-coherent modules on `((X/S)_•)_Zar`,
i.e. on `zariskiRingedSite f.simplicialScheme`. -/
@[stacks 07TL]
theorem QCoh.pullback_isEquivalence {X S : Scheme.{u}} (f : X ⟶ S) [IsSplitEpi f] :
    (QCoh.pullback f).IsEquivalence :=
  sorry

end AlgebraicGeometry.SimplicialObject
