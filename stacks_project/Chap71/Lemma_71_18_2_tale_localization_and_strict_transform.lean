/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap71.Definition_71_17_1_Blowup
public import stacks_project.Chap71.Definition_71_18_1_StrictTransform

/-!
# Étale localization of strict transforms of algebraic spaces

In the situation of Definition 71.18.1, an étale commutative square of
algebraic spaces with scheme vertices localizes blowups and strict transforms
of spaces and modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inverse image of a closed subspace with quasi-coherent ideal sheaf again
has quasi-coherent ideal sheaf. -/
instance instIsQuasiCoherent_inverseImage_idealSheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsQuasiCoherent Z.idealSheaf] (f : Y ⟶ X) :
    IsQuasiCoherent (Z.inverseImage f).idealSheaf :=
  sorry

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable (Z : ClosedSubspace B) [IsQuasiCoherent Z.idealSheaf]
variable (πB : Blowup.along Z) (f : X ⟶ B)
variable {U V : Over S} (α : ofOver U ⟶ X) (β : ofOver V ⟶ B) (h : U ⟶ V)
variable (πV : Blowup.along (Z.inverseImage β))

/-- The two paths around the localization cube from `U ×_V V'` to `B` agree. -/
theorem strictTransformAmbientMap_comm (g' : πV.space ⟶ πB.space)
    (wα : α ≫ f = ofOverMap h ≫ β)
    (wg' : g' ≫ πB.hom = πV.hom ≫ β) :
    (pullback.fst (ofOverMap h) πV.hom ≫ α) ≫ f =
      (pullback.snd (ofOverMap h) πV.hom ≫ g') ≫ πB.hom :=
  sorry

/-- The comparison morphism `U ×_V V' ⟶ X ×_B B'` induced by an étale
localization square and a comparison `g' : V' ⟶ B'`. -/
def strictTransformAmbientMap (g' : πV.space ⟶ πB.space)
    (wα : α ≫ f = ofOverMap h ≫ β)
    (wg' : g' ≫ πB.hom = πV.hom ≫ β) :
    pullback (ofOverMap h) πV.hom ⟶ pullback f πB.hom :=
  pullback.lift
    (pullback.fst (ofOverMap h) πV.hom ≫ α)
    (pullback.snd (ofOverMap h) πV.hom ≫ g')
    (strictTransformAmbientMap_comm Z πB f α β h πV g' wα wg')

/-- The comparison morphism projects to `α` on the `X`-factor. -/
theorem strictTransformAmbientMap_fst (g' : πV.space ⟶ πB.space)
    (wα : α ≫ f = ofOverMap h ≫ β)
    (wg' : g' ≫ πB.hom = πV.hom ≫ β) :
    strictTransformAmbientMap Z πB f α β h πV g' wα wg' ≫
        pullback.fst f πB.hom =
      pullback.fst (ofOverMap h) πV.hom ≫ α :=
  sorry

/-- The comparison morphism projects to `g'` on the `B'`-factor. -/
theorem strictTransformAmbientMap_snd (g' : πV.space ⟶ πB.space)
    (wα : α ≫ f = ofOverMap h ≫ β)
    (wg' : g' ≫ πB.hom = πV.hom ≫ β) :
    strictTransformAmbientMap Z πB f α β h πV g' wα wg' ≫
        pullback.snd f πB.hom =
      pullback.snd (ofOverMap h) πV.hom ≫ g' :=
  sorry

/-- Lemma 71.18.2 (Étale localization and strict transform) (1): in the
situation of Definition 71.18.1, a commutative square with scheme vertices
`U`, `V` and étale horizontal arrows has cartesian blowup comparison
`V' = V ×_B B'`, and the maps `V' ⟶ B'` and `U ×_V V' ⟶ X ×_B B'` are étale. -/
@[stacks 0863]
theorem strictTransform_etale_exists_isPullback [Etale α] [Etale β]
    (sq : CommSq α (ofOverMap h) f β) :
    ∃ (g' : πV.space ⟶ πB.space) (hg' : IsPullback g' πV.hom πB.hom β),
      Etale g' ∧
        Etale (strictTransformAmbientMap Z πB f α β h πV g' sq.w hg'.w) :=
  sorry

/-- Lemma 71.18.2 (Étale localization and strict transform) (2): the strict
transform `U'` of `U` relative to `V' ⟶ V` is cartesian over the strict
transform `X'` of `X` relative to `B' ⟶ B`, as `U' = X' ×_X U`. -/
@[stacks 0863]
theorem strictTransform_etale_isPullback [Etale α] [Etale β]
    [QuasiCompact
      (strictTransformOpenComplement πB.hom (Z.inverseImage πB.hom) f).ι]
    [QuasiCompact
      (strictTransformOpenComplement πV.hom
        ((Z.inverseImage β).inverseImage πV.hom) (ofOverMap h)).ι]
    (sq : CommSq α (ofOverMap h) f β)
    (g' : πV.space ⟶ πB.space) (hg' : IsPullback g' πV.hom πB.hom β) :
    ∃ i :
      (strictTransform πV.hom ((Z.inverseImage β).inverseImage πV.hom)
          (ofOverMap h)).X ⟶
        (strictTransform πB.hom (Z.inverseImage πB.hom) f).X,
      IsPullback i
        ((strictTransform πV.hom ((Z.inverseImage β).inverseImage πV.hom)
            (ofOverMap h)).ι ≫
          pullback.fst (ofOverMap h) πV.hom)
        ((strictTransform πB.hom (Z.inverseImage πB.hom) f).ι ≫
          pullback.fst f πB.hom)
        α :=
  sorry

/-- The strict transform of `U` is the inverse image of the strict transform of
`X` along the comparison `U ×_V V' ⟶ X ×_B B'`. -/
theorem strictTransform_etale_inverseImage [Etale α] [Etale β]
    [QuasiCompact
      (strictTransformOpenComplement πB.hom (Z.inverseImage πB.hom) f).ι]
    [QuasiCompact
      (strictTransformOpenComplement πV.hom
        ((Z.inverseImage β).inverseImage πV.hom) (ofOverMap h)).ι]
    (sq : CommSq α (ofOverMap h) f β)
    (g' : πV.space ⟶ πB.space) (hg' : IsPullback g' πV.hom πB.hom β) :
    ∃ i :
      (strictTransform πV.hom ((Z.inverseImage β).inverseImage πV.hom)
          (ofOverMap h)).X ⟶
        (strictTransform πB.hom (Z.inverseImage πB.hom) f).X,
      IsPullback i
        (strictTransform πV.hom ((Z.inverseImage β).inverseImage πV.hom)
          (ofOverMap h)).ι
        (strictTransform πB.hom (Z.inverseImage πB.hom) f).ι
        (strictTransformAmbientMap Z πB f α β h πV g' sq.w hg'.w) :=
  sorry

/-- Lemma 71.18.2 (Étale localization and strict transform) (3): for a
quasi-coherent `𝒪_X`-module `F`, the restriction of the strict transform `F'`
to `U ×_V V'` is the strict transform of `F|_U` relative to `V' ⟶ V`. -/
@[stacks 0863]
theorem strictTransformModule_etale_pullback [Etale α] [Etale β]
    (sq : CommSq α (ofOverMap h) f β)
    (g' : πV.space ⟶ πB.space) (hg' : IsPullback g' πV.hom πB.hom β)
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIsomorphic
      ((Modules.pullback
          (strictTransformAmbientMap Z πB f α β h πV g' sq.w hg'.w)).obj
        (strictTransformModule πB.hom (Z.inverseImage πB.hom) f F))
      (strictTransformModule πV.hom ((Z.inverseImage β).inverseImage πV.hom)
        (ofOverMap h) ((Modules.pullback α).obj F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

