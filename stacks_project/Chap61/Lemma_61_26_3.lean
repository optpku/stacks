module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ExtensionByZero
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

/- Lemma 61.26.3: if `j : U ⟶ X` is a weakly étale morphism of schemes,
`i : Z ⟶ X` is a closed immersion such that `pullback j i` is empty, and
`V` is an affine object of `X.ProEt` such that every point of `V` specializes
to a point of `pullback i V.hom`, then
`IsZero (((abelianExtensionByZero j).obj F).obj.obj (op V))` for every
abelian sheaf `F` on `U.ProEt`. -/
@[stacks 09AG] #check
  (AlgebraicGeometry.Scheme.ProEt.abelianExtensionByZero_sections_isZero :
    ∀ {U X Z : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    [IsEmpty (pullback j i : Scheme.{u})]
    (V : X.ProEt) [IsAffine V.left]
    (hV : ∀ x : V.left,
      ∃ z : (pullback i V.hom : Scheme.{u}),
        x ⤳ (pullback.snd i V.hom) z)
    [∀ F : U.ProEtᵒᵖ ⥤ AddCommGrpCat.{w},
      (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) AddCommGrpCat.{w}]
    (F : Sheaf (topology U) AddCommGrpCat.{w}),
    IsZero (((abelianExtensionByZero j).obj F).obj.obj (op V)))

end AlgebraicGeometry.Scheme.ProEt
