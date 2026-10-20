/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_1_Product
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap78.Definition_78_5_1_Group

/-!
# Multiplicative group algebraic space

The multiplicative group algebraic space over an algebraic space `B` over a scheme `S` is the
fibre product `B ×_S 𝔾ₘ[S]`. Its `B`-points on a scheme `T` over `B` are the global units
`Γ(T.left, ⊤)ˣ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open CartesianMonoidalCategory (lift fst snd)
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.ofScheme :
  ∀ (S : Scheme.{u}),
    AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.ofScheme_eq :
  ∀ (S : Scheme.{u}),
    ofScheme S = ofOver (AlgebraicGeometry.MultiplicativeGroup.baseChange S).X)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.space :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.space_functorOfPoints :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    (space B).functorOfPoints = (B.functorOfPoints ⨯ (ofScheme S).functorOfPoints))

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.hom :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    space B ⟶ B)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.hom_eq_fst :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    hom B = (Limits.prod.fst : B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶
      B.functorOfPoints))

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.asOver :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    Over B)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.asOver_eq :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    asOver B = Over.mk (hom B))

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.asOver_hom :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    (asOver B).hom = hom B)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.ofUnit :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S} (t : ofOver T ⟶ B)
    (unit : Γ(T.left, ⊤)ˣ),
    Over.mk t ⟶ asOver B)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.ofUnit_left :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ B) (unit : Γ(T.left, ⊤)ˣ),
    (ofUnit t unit).left = Limits.prod.lift (X := B.functorOfPoints) t
      (yoneda.map ((AlgebraicGeometry.MultiplicativeGroup.baseChangeHomEquiv S T).symm unit)))

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.toUnit :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S} (t : ofOver T ⟶ B)
    (point : Over.mk t ⟶ asOver B),
    Γ(T.left, ⊤)ˣ)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.homOverEquiv :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S} (t : ofOver T ⟶ B),
    (Over.mk t ⟶ asOver B) ≃ Γ(T.left, ⊤)ˣ)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.homOverEquiv_apply :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ B) (point : Over.mk t ⟶ asOver B),
    homOverEquiv t point = toUnit t point)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.ofSchemeMul :
  ∀ {S : Scheme.{u}} {E : AlgebraicSpace S} (first second : E ⟶ ofScheme S),
    E ⟶ ofScheme S)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.ofSchemeMul_app :
  ∀ {S : Scheme.{u}} {E : AlgebraicSpace S}
    (first second : E ⟶ ofScheme S) (T : (Over S)ᵒᵖ) (point : E.functorOfPoints.obj T),
    (ofSchemeMul first second).app T point = lift (first.app T point) (second.app T point) ≫
      μ[(AlgebraicGeometry.MultiplicativeGroup.baseChange S).X])

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.oneHom :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    𝟙_ (Over B) ⟶ asOver B)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.oneHom_left :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    (oneHom B).left = Limits.prod.lift (X := B.functorOfPoints) (𝟙 B.functorOfPoints) (ofSchemeOne B))

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.mulHom :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    asOver B ⊗ asOver B ⟶ asOver B)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.mulHom_left :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    (mulHom B).left = Limits.prod.lift (X := B.functorOfPoints) (asOver B ⊗ asOver B).hom
      (ofSchemeMul
        ((fst (asOver B) (asOver B)).left ≫ (Limits.prod.snd :
          B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ (ofScheme S).functorOfPoints))
        ((snd (asOver B) (asOver B)).left ≫ (Limits.prod.snd :
          B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ (ofScheme S).functorOfPoints))))

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.invHom :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    asOver B ⟶ asOver B)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.invHom_left :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    (invHom B).left = Limits.prod.lift (X := B.functorOfPoints) (hom B)
      ((Limits.prod.snd :
        B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ (ofScheme S).functorOfPoints) ≫
          yoneda.map (ι[(AlgebraicGeometry.MultiplicativeGroup.baseChange S).X])))

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.instGrpObj_asOver :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    GrpObj (asOver B))

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.groupSpace :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    GroupAlgebraicSpace B)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.groupSpace_X :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    (groupSpace B).X = asOver B)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.homOverMulEquiv :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ B),
    (Over.mk t ⟶ asOver B) ≃* Γ(T.left, ⊤)ˣ)

#check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.homOverMulEquiv_apply :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ B) (point : Over.mk t ⟶ asOver B),
    homOverMulEquiv t point = toUnit t point)
