/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap76.Definition_76_12_1_Neighbourhood
public import stacks_project.Chap76.Lemma_76_5_3_Map

/-!
# Conormal comparison for first-order infinitesimal neighbourhoods

The identity square relating an immersion of algebraic spaces to its first-order
infinitesimal neighbourhood induces a canonical morphism of conormal sheaves
`Hom.conormalSheaf i ⟶ Hom.conormalSheaf (fromSource i 1)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom.InfinitesimalNeighbourhood

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S}

/-- The identity square relating an immersion `i : Z ⟶ X` to the closed immersion
from `Z` into its first-order infinitesimal neighbourhood `space i 1`. -/
theorem firstOrderConormalSq (i : Z ⟶ X) [IsImmersion i] :
    CommSq (𝟙 Z) (fromSource i 1) i (toAmbient i 1) :=
  sorry

/-- The canonical comparison `Hom.conormalSheaf i ⟶ Hom.conormalSheaf (fromSource i 1)`
obtained from `Hom.Conormal.map` of `firstOrderConormalSq i`, after transporting
along `SmallEtaleModuleGlueing.modulesPullbackId`. -/
noncomputable def conormalComparison (i : Z ⟶ X) [IsImmersion i] :
    Hom.conormalSheaf i ⟶ Hom.conormalSheaf (fromSource i 1) :=
  (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (Hom.conormalSheaf i) ≫
    Hom.Conormal.map (firstOrderConormalSq i)

/-- `conormalComparison` is the identity-pullback correction of
`Hom.Conormal.map (firstOrderConormalSq i)`. -/
theorem conormalComparison_eq (i : Z ⟶ X) [IsImmersion i] :
    conormalComparison i =
      (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (Hom.conormalSheaf i) ≫
        Hom.Conormal.map (firstOrderConormalSq i) :=
  sorry

/-- Source-semantic packaging: `conormalComparison` is the Lemma 76.5.3 map of the
identity square, after the identity-pullback correction. -/
theorem conormalComparison_spec (i : Z ⟶ X) [IsImmersion i] :
    Hom.Conormal.IsMap (firstOrderConormalSq i)
        (Hom.Conormal.map (firstOrderConormalSq i)) ∧
      conormalComparison i =
        (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (Hom.conormalSheaf i) ≫
          Hom.Conormal.map (firstOrderConormalSq i) :=
  sorry

end Hom.InfinitesimalNeighbourhood

end AlgebraicGeometry.AlgebraicSpace
