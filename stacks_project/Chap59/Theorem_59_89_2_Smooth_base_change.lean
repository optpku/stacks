module

public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import stacks_project.Chap59.Lemma_59_29_7
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Smooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]

/- Theorem 59.89.2 (Smooth base change): smooth inverse image commutes with
higher étale direct image for stalkwise torsion of orders invertible on the base. -/
@[stacks 0EYU] #check
  (AlgebraicGeometry.Scheme.Hom.higherDirectImageBaseChange_isIso_of_smooth :
    ∀ {X S T Y : Scheme.{u}} (f : X ⟶ S) [Smooth f] (g : T ⟶ S)
      [QuasiCompact g] [QuasiSeparated g] (h : Y ⟶ X) (e : Y ⟶ T)
      (h_cart : IsPullback h e f g)
      {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}},
      IsTorsionWithOrdersInvertibleOn S F → ∀ q : ℕ,
        IsIso (higherDirectImageBaseChange g f h e h_cart.flip F q))

end

end
