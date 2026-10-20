module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.CommRingAdjunction
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Composition of pullback of quasi-coherent algebras

Successive scalar extensions of inverse-image commutative-ring sheaves identify
with scalar extension along the composite morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

variable {S : Scheme.{u}}

/-- Equal morphisms of algebraic spaces induce isomorphic algebra pullbacks. -/
def pullbackCongr {Y W : AlgebraicSpace S} {f g : Y ⟶ W} (h : f = g) :
    pullback f ≅ pullback g :=
  eqToIso (congrArg pullback h)

/-- Inverse image of commutative-ring sheaves is a left adjoint. -/
instance instIsLeftAdjoint_pullbackSheafFunctor {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    (pullbackSheafFunctor f).IsLeftAdjoint :=
  (ConormalAlgebra.commRingInverseImageAdjunction f).isLeftAdjoint

/-- Forward sheaf of successive algebra pullbacks, compared with pullback along the composite. -/
def pullbackCompSheafHom {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T)
    (A : T.QcAlgebraUnder) :
    ((pullback f).obj ((pullback g).obj A)).obj.right ⟶
      ((pullback (f ≫ g)).obj A).obj.right := by
  refine
    let F := pullbackSheafFunctor f
    let Gfun := pullbackSheafFunctor g
    let Fg := pullbackSheafFunctor (f ≫ g)
    let inner := (pullbackUnder g).obj A.obj
    let composite := (pullbackUnder (f ≫ g)).obj A.obj
    pushout.desc
      ((asIso (pushoutComparison F (Gfun.map A.obj.hom)
            (AlgebraicSpace.commInverseImageStructureSheafMap g))).inv ≫
        pushout.desc
          ((ConormalAlgebra.commRingInverseImageCompIso f g).hom.app A.obj.right ≫
            pushout.inl (Fg.map A.obj.hom) (AlgebraicSpace.commInverseImageStructureSheafMap (f ≫ g)))
          (AlgebraicSpace.commInverseImageStructureSheafMap f ≫ composite.hom)
          ?_)
      composite.hom
      ?_
  all_goals sorry

/-- Reverse sheaf of pullback along a composite, compared with successive algebra pullbacks. -/
def pullbackCompSheafInv {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T)
    (A : T.QcAlgebraUnder) :
    ((pullback (f ≫ g)).obj A).obj.right ⟶
      ((pullback f).obj ((pullback g).obj A)).obj.right := by
  refine
    let F := pullbackSheafFunctor f
    let Gfun := pullbackSheafFunctor g
    let Fg := pullbackSheafFunctor (f ≫ g)
    let inner := (pullbackUnder g).obj A.obj
    let nested := (pullbackUnder f).obj inner
    pushout.desc
      ((ConormalAlgebra.commRingInverseImageCompIso f g).inv.app A.obj.right ≫
        F.map (pushout.inl (Gfun.map A.obj.hom) (AlgebraicSpace.commInverseImageStructureSheafMap g)) ≫
          pushout.inl (F.map inner.hom) (AlgebraicSpace.commInverseImageStructureSheafMap f))
      nested.hom
      ?_
  all_goals sorry

/-- The sheaf comparison of successive algebra pullbacks commutes with structure maps. -/
theorem pullbackCompSheafHom_w {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T)
    (A : T.QcAlgebraUnder) :
    ((pullback f).obj ((pullback g).obj A)).obj.hom ≫
        pullbackCompSheafHom f g A =
      ((pullback (f ≫ g)).obj A).obj.hom :=
  sorry

/-- The reverse sheaf comparison of successive algebra pullbacks commutes with structure maps. -/
theorem pullbackCompSheafInv_w {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T)
    (A : T.QcAlgebraUnder) :
    ((pullback (f ≫ g)).obj A).obj.hom ≫ pullbackCompSheafInv f g A =
      ((pullback f).obj ((pullback g).obj A)).obj.hom :=
  sorry

/-- Composition of algebra pullbacks identifies with pullback along the composite. -/
def pullbackComp {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T) :
    pullback g ⋙ pullback f ≅
      pullback (f ≫ g) := by
  refine
    NatIso.ofComponents
      (fun A ↦
        { hom :=
            homMk (Under.homMk (pullbackCompSheafHom f g A) (pullbackCompSheafHom_w f g A))
          inv :=
            homMk (Under.homMk (pullbackCompSheafInv f g A) (pullbackCompSheafInv_w f g A))
          hom_inv_id := ?_
          inv_hom_id := ?_ })
      ?_
  all_goals sorry
end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
