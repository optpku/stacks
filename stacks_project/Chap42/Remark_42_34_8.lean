/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/- Remark 42.34.8: For a closed immersion `i : Z ⟶ X`, capping a class on `Z`
obtained by restriction agrees with capping after proper pushforward along `i`. -/
@[stacks 0FA1] #check
  (AlgebraicGeometry.BivariantClass.restrictToSource_cap :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      {X Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Z.hom]
      (i : Z ⟶ X) [IsClosedImmersion i.left] (p k : ℤ)
      (c : BivariantClass δ i p) (α : RelativeChow δ Z k),
      (restrictToSource δ i p c).cap (𝟙 Z) (𝟙 Z) (𝟙 Z)
          IsPullback.of_id_snd k α =
        c.cap (𝟙 Z) i (𝟙 X) (IsPullback.id_horiz i.left) k
          (ChowGroup.map δ Z X i k α))

end AlgebraicGeometry.BivariantClass
