module

public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap76.Lemma_76_9_2_Thickening
public import stacks_project.Chap88.Definition_88_21_1_Formal
public import stacks_project.Chap87.Lemma_87_27_3_ClosedImmersion

/-!
# Closed immersions from monomorphisms through the reduction

A morphism of formal algebraic spaces that is representable by algebraic
spaces, a monomorphism, through which the reduction of the target factors,
and that is locally of finite type or has locally Noetherian target, is a
closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The morphism `ιY : Yred.functorOfPoints ⟶ Y` is the reduction of a formal
algebraic space `Y` when `Yred` is reduced, `ιY` is a representable thickening,
and maps from reduced algebraic spaces factor uniquely through it. -/
@[mk_iff]
class IsReduction {S : Scheme.{u}} {Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace Y] (Yred : AlgebraicSpace S)
    (ιY : Yred.functorOfPoints ⟶ Y) : Prop where
  /-- The reduction is reduced in the étale-local sense. -/
  isReduced : AlgebraicSpace.hasEtaleLocal
    (IsReduced : ObjectProperty Scheme.{u}) Yred
  /-- The structure morphism is representable by algebraic spaces. -/
  representable : AlgebraicSpace.representableByAlgebraicSpaces ιY
  /-- Yoneda pullbacks of the structure morphism are thickenings. -/
  isThickening : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
    AlgebraicSpace.IsThickening
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom representable ξ)
  /-- A morphism from a reduced algebraic space into `Y` factors uniquely
  through `ιY`. -/
  liftUnique : ∀ {U : AlgebraicSpace S},
    AlgebraicSpace.hasEtaleLocal
      (IsReduced : ObjectProperty Scheme.{u}) U →
    ∀ (k : U.functorOfPoints ⟶ Y),
      ∃! h : U.functorOfPoints ⟶ Yred.functorOfPoints, h ≫ ιY = k

namespace IsReduction

/-- A reduced affine scheme over `S`, viewed as a formal algebraic space, is its
own reduction. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] [IsReduced U.left] :
    IsReduction (AlgebraicSpace.ofOver U) (𝟙 (yoneda.obj U)) :=
  sorry

/-- A reduction of a formal algebraic space is reduced, the structure morphism
is a representable thickening, and maps from reduced algebraic spaces factor
uniquely through it. -/
theorem spec {S : Scheme.{u}} {Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace Y] {Yred : AlgebraicSpace S}
    {ιY : Yred.functorOfPoints ⟶ Y} [hY : IsReduction Yred ιY] :
    AlgebraicSpace.hasEtaleLocal
        (IsReduced : ObjectProperty Scheme.{u}) Yred ∧
      AlgebraicSpace.representableByAlgebraicSpaces ιY ∧
        (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
          AlgebraicSpace.IsThickening
            (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom
              hY.representable ξ)) ∧
          ∀ {U : AlgebraicSpace S},
            AlgebraicSpace.hasEtaleLocal
              (IsReduced : ObjectProperty Scheme.{u}) U →
            ∀ (k : U.functorOfPoints ⟶ Y),
              ∃! h : U.functorOfPoints ⟶ Yred.functorOfPoints, h ≫ ιY = k :=
  sorry

end IsReduction

namespace ClosedImmersion

/-- Lemma 87.27.7: a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S` that is representable by algebraic spaces, a monomorphism, through
which the inclusion `Y_red ⟶ Y` factors, and that is locally of finite type on
Yoneda pullbacks or has locally Noetherian target, is a closed immersion. -/
@[stacks 0GHZ]
theorem of_mono_of_reduction {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) [Mono f]
    (h_rep : AlgebraicSpace.representableByAlgebraicSpaces f)
    {Yred : AlgebraicSpace S} (ιY : Yred.functorOfPoints ⟶ Y)
    [IsReduction Yred ιY] (g : Yred.functorOfPoints ⟶ X)
    (h_factor : g ≫ f = ιY)
    (h_lft_or_noetherian :
      (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
          AlgebraicSpace.LocallyOfFiniteType
            (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom h_rep ξ)) ∨
        IsLocallyNoetherian Y) :
    ClosedImmersion f :=
  sorry

/-- A monomorphism of formal algebraic spaces that is locally of finite type on
Yoneda pullbacks, and through which the inclusion of the reduction of the
target factors, is a closed immersion. -/
theorem of_mono_of_reduction_locallyOfFiniteType {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) [Mono f]
    (h_rep : AlgebraicSpace.representableByAlgebraicSpaces f)
    {Yred : AlgebraicSpace S} (ιY : Yred.functorOfPoints ⟶ Y)
    [IsReduction Yred ιY] (g : Yred.functorOfPoints ⟶ X)
    (h_factor : g ≫ f = ιY)
    (h_lft : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.LocallyOfFiniteType
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom h_rep ξ)) :
    ClosedImmersion f :=
  sorry

/-- A representable monomorphism of formal algebraic spaces with locally
Noetherian target, through which the inclusion of the reduction of the target
factors, is a closed immersion. -/
theorem of_mono_of_reduction_locallyNoetherian {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Mono f]
    (h_rep : AlgebraicSpace.representableByAlgebraicSpaces f)
    {Yred : AlgebraicSpace S} (ιY : Yred.functorOfPoints ⟶ Y)
    [IsReduction Yred ιY] (g : Yred.functorOfPoints ⟶ X)
    (h_factor : g ≫ f = ιY) :
    ClosedImmersion f :=
  sorry

end ClosedImmersion

end AlgebraicGeometry.FormalAlgebraicSpace
