module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Sections
import StacksCheckRecall

/-!
# Lemma 61.25.5

If `i : Z ⟶ X` is a closed immersion and `U` is an affine weakly contractible
object of `X.ProEt` whose points all specialize into `U ×_X Z`, then inverse
image along `smallProetalePullback i` identifies sections of abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt
open Opposite

universe u

/- Lemma 61.25.5: inverse image along a closed immersion preserves sections on
affine weakly contractible pro-étale objects whose points specialize into the
base change. -/
@[stacks 09AC] #check
  (AlgebraicGeometry.Scheme.ProEt.smallInverseImage_obj_to_isIso :
    ∀ {Z X : Scheme.{u}} (i : Z ⟶ X)
      [HasSheafify (topology X) AddCommGrpCat.{u + 1}]
      [HasSheafify (topology Z) AddCommGrpCat.{u + 1}]
      [∀ P : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
        (smallProetalePullback i).op.HasLeftKanExtension P]
      [IsClosedImmersion i] (U : X.ProEt)
      [IsAffine U.left] [(topology X).IsWeaklyContractible U]
      (hU : ∀ x : U.left,
        ∃ z : (pullback U.hom i : Scheme.{u}),
          x ⤳ (pullback.fst U.hom i) z)
      (F : Sheaf (topology X) AddCommGrpCat.{u + 1}),
      IsIso (AlgebraicGeometry.Scheme.ProEt.smallInverseImage_obj_to i F U))
