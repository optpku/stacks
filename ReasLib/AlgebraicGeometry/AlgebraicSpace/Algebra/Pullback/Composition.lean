/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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

/-- Descent from an inverse-image pushout, using the given adjunction on both legs. -/
def inverseImagePushoutDesc {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    {R A B : Sheaf (smallEtaleTopology W) CommRingCat.{u}}
    {Q : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    (a : R ⟶ A) (b : R ⟶ B)
    (h : (pullbackSheafFunctor f).obj A ⟶ Q)
    (k : (pullbackSheafFunctor f).obj B ⟶ Q)
    (w : (pullbackSheafFunctor f).map a ≫ h = (pullbackSheafFunctor f).map b ≫ k) :
    (pullbackSheafFunctor f).obj (pushout a b) ⟶ Q :=
  let adj := ConormalAlgebra.commRingInverseImageAdjunction f
  (adj.homEquiv _ _).symm
    (pushout.desc ((adj.homEquiv _ _) h) ((adj.homEquiv _ _) k) (by
      rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left]
      exact congrArg (adj.homEquiv R Q) w))

/-- Descent through the given adjunction has the prescribed right leg. -/
theorem inverseImagePushoutDesc_inr {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    {R A B : Sheaf (smallEtaleTopology W) CommRingCat.{u}}
    {Q : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    (a : R ⟶ A) (b : R ⟶ B)
    (h : (pullbackSheafFunctor f).obj A ⟶ Q)
    (k : (pullbackSheafFunctor f).obj B ⟶ Q)
    (w : (pullbackSheafFunctor f).map a ≫ h = (pullbackSheafFunctor f).map b ≫ k) :
    (pullbackSheafFunctor f).map (pushout.inr a b) ≫
        inverseImagePushoutDesc f a b h k w = k := by
  change (commRingInverseImage f).map (pushout.inr a b) ≫ _ = _
  apply ((ConormalAlgebra.commRingInverseImageAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  simp only [inverseImagePushoutDesc,
    Equiv.apply_symm_apply, pushout.inr_desc]

/-- The two scalar-extension legs agree before descent through the inner pushout. -/
theorem pullbackCompSheafCocone_w {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T)
    (A : T.QcAlgebraUnder) :
    let F := pullbackSheafFunctor f
    let Gfun := pullbackSheafFunctor g
    let Fg := pullbackSheafFunctor (f ≫ g)
    let composite := (pullbackUnder (f ≫ g)).obj A.obj
    F.map (Gfun.map A.obj.hom) ≫
        ((ConormalAlgebra.commRingInverseImageCompIso f g).hom.app A.obj.right ≫
          pushout.inl (Fg.map A.obj.hom)
            (AlgebraicSpace.commInverseImageStructureSheafMap (f ≫ g))) =
      F.map (AlgebraicSpace.commInverseImageStructureSheafMap g) ≫
        (AlgebraicSpace.commInverseImageStructureSheafMap f ≫ composite.hom) :=
  sorry

/-- Forward sheaf of successive algebra pullbacks, using the given inverse-image
adjunction and pushout descent rather than selecting an inverse comparison. -/
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
      (inverseImagePushoutDesc f (Gfun.map A.obj.hom)
          (AlgebraicSpace.commInverseImageStructureSheafMap g)
          ((ConormalAlgebra.commRingInverseImageCompIso f g).hom.app A.obj.right ≫
            pushout.inl (Fg.map A.obj.hom) (AlgebraicSpace.commInverseImageStructureSheafMap (f ≫ g)))
          (AlgebraicSpace.commInverseImageStructureSheafMap f ≫ composite.hom)
          (pullbackCompSheafCocone_w f g A))
      composite.hom
      ?_
  exact inverseImagePushoutDesc_inr f _ _ _ _ _

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
  by
    change pushout.inr _ _ ≫ pushout.desc _ _ _ = _
    exact pushout.inr_desc _ _ _

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
