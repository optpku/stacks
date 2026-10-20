/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective

/-! # Small étale sheaves along integral universally injective morphisms -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A sheaf of sets on `X_étale` restricts to the terminal sheaf `*` on the open complement
`|X| \ f(|Y|)` of an integral morphism `f : Y ⟶ X`. -/
def restrictsToTerminalOnImageComplement {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) : Prop :=
  Nonempty
    ((@etaleRestrictionSheaf _ _ _ (imageComplementι f)
        (Etale.ofIsOpenImmersion (h := (imageComplementSubspace f).isOpenImmersion))
        (Type (u + 1)) _).obj F ≅
      ⊤_ (Sheaf (smallEtaleTopology (imageComplement f)) (Type (u + 1))))

/-- Restriction to `|X| \ f(|Y|)` is isomorphic to `*` if and only if the restricted sheaf is
terminal. -/
theorem restrictsToTerminalOnImageComplement_iff {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    restrictsToTerminalOnImageComplement f F ↔
      Nonempty
        (IsTerminal
          ((@etaleRestrictionSheaf _ _ _ (imageComplementι f)
            (Etale.ofIsOpenImmersion (h := (imageComplementSubspace f).isOpenImmersion))
            (Type (u + 1)) _).obj F)) :=
  sorry

variable {X Y : AlgebraicSpace S} (f : Y ⟶ X)
variable [IsIntegralHom f] [UniversallyInjective f]

/-- Small étale pushforward of sheaves of sets along a universally injective
integral morphism of algebraic spaces is full. -/
@[instance]
theorem sheafPushforward_integralUnivInj_type_full :
    (sheafPushforward (Type (u + 1)) f).Full := sorry

/-- Small étale pushforward of sheaves of sets along a universally injective
integral morphism of algebraic spaces is faithful. -/
@[instance]
theorem sheafPushforward_integralUnivInj_type_faithful :
    (sheafPushforward (Type (u + 1)) f).Faithful := sorry

/-- The essential image of small étale set-valued pushforward along a
universally injective integral morphism consists of sheaves whose restriction to
`|X| \ f(|Y|)` is isomorphic to the terminal sheaf `*`. -/
theorem mem_essImage_sheafPushforward_integralUnivInj_type_iff
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (sheafPushforward (Type (u + 1)) f).essImage F ↔
      restrictsToTerminalOnImageComplement f F := sorry

/-- Small étale inverse image of sheaves of sets is a left inverse of
pushforward along a universally injective integral morphism, equivalently the adjunction
counit is invertible. -/
@[instance]
theorem isIso_counit_sheafPushforward_integralUnivInj_type
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology Y) (Type (u + 1))] :
    IsIso (sheafAdjunction (Type (u + 1)) f).counit := sorry

/-- Small étale pushforward of abelian sheaves along a universally injective
integral morphism of algebraic spaces is full. -/
@[instance]
theorem sheafPushforward_integralUnivInj_ab_full :
    (sheafPushforward AddCommGrpCat.{u + 1} f).Full := sorry

/-- Small étale pushforward of abelian sheaves along a universally injective
integral morphism of algebraic spaces is faithful. -/
@[instance]
theorem sheafPushforward_integralUnivInj_ab_faithful :
    (sheafPushforward AddCommGrpCat.{u + 1} f).Faithful := sorry

/-- The essential image of small étale abelian pushforward along a
universally injective integral morphism consists of abelian sheaves on `X_étale` whose
support is contained in `f(|Y|)`. -/
theorem mem_essImage_sheafPushforward_integralUnivInj_ab_iff
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (sheafPushforward AddCommGrpCat.{u + 1} f).essImage F ↔
      abelianSheafSupport F ⊆ pointsImage f := sorry

/-- Small étale inverse image of abelian sheaves is a left inverse of
pushforward along a universally injective integral morphism, equivalently the adjunction
counit is invertible. -/
@[instance]
theorem isIso_counit_sheafPushforward_integralUnivInj_ab
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleBaseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology Y) AddCommGrpCat.{u + 1}] :
    IsIso (sheafAdjunction AddCommGrpCat.{u + 1} f).counit := sorry

end AlgebraicGeometry.AlgebraicSpace
