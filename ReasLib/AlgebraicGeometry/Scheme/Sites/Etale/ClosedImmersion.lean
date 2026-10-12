/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport
public import Mathlib.CategoryTheory.Sites.Pullback

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The stalk of the small-étale pushforward of a sheaf of sets along a closed
immersion at a geometric point outside the closed image is equivalent to
the singleton type `PUnit`. -/
theorem stalk_pushforward_closedImmersion_outside
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (G : Sheaf Z.smallEtaleTopology (Type u))
    (xbar : Scheme.GeometricPoint X)
    (h_mem : xbar.image ∉ Set.range i.base) :
    Nonempty
      (stalk xbar
          (((Scheme.smallEtalePullback i).sheafPushforwardContinuous
              (Type u) X.smallEtaleTopology Z.smallEtaleTopology).obj G).1 ≃
        PUnit) := sorry

/-- A geometric lift through a closed immersion identifies the stalk of the
small-étale pushforward of a sheaf of sets with its stalk at the lifted
geometric point. -/
theorem stalk_pushforward_closedImmersion_inside
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (G : Sheaf Z.smallEtaleTopology (Type u))
    (xbar : Scheme.GeometricPoint X)
    (h_mem : xbar.image ∈ Set.range i.base)
    (s : Spec (.of xbar.K) ⟶ Z)
    (hs : s ≫ i = xbar.hom) :
    Nonempty
      (stalk xbar
          (((Scheme.smallEtalePullback i).sheafPushforwardContinuous
              (Type u) X.smallEtaleTopology Z.smallEtaleTopology).obj G).1 ≃
        stalk (@Scheme.GeometricPoint.of Z xbar.K inferInstance xbar.isAlgClosed s) G.1) := sorry

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- A sheaf of sets on the small étale site restricts to the terminal sheaf on the open
complement of a closed immersion. -/
def restrictsToTerminalOnComplement
    [HasWeakSheafify (closedImmersionComplement i).toScheme.smallEtaleTopology (Type u)]
    [∀ P : X.Etaleᵒᵖ ⥤ Type u,
      (Scheme.smallEtalePullback (closedImmersionComplement i).ι).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (Type u)) : Prop :=
  Nonempty
    (((Scheme.smallEtalePullback (closedImmersionComplement i).ι).sheafPullback
          (Type u) X.smallEtaleTopology
          (closedImmersionComplement i).toScheme.smallEtaleTopology).obj F ≅
      ⊤_ (Sheaf (closedImmersionComplement i).toScheme.smallEtaleTopology (Type u)))

/-- Restriction to the complement of a closed immersion is isomorphic to the terminal
sheaf if and only if the restricted sheaf is terminal. -/
theorem restrictsToTerminalOnComplement_iff
    [HasWeakSheafify (closedImmersionComplement i).toScheme.smallEtaleTopology (Type u)]
    [∀ P : X.Etaleᵒᵖ ⥤ Type u,
      (Scheme.smallEtalePullback (closedImmersionComplement i).ι).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    restrictsToTerminalOnComplement i F ↔
      Nonempty
        (IsTerminal
          (((Scheme.smallEtalePullback (closedImmersionComplement i).ι).sheafPullback
              (Type u) X.smallEtaleTopology
              (closedImmersionComplement i).toScheme.smallEtaleTopology).obj F)) := sorry

/-- Small-étale direct image of sheaves of sets along a closed immersion is full. -/
@[stacks 04CA, instance]
theorem smallEtalePushforward_closedImmersion_type_full :
    (Scheme.smallEtaleDirectImage.{u, u} i).Full := sorry

/-- Small-étale direct image of sheaves of sets along a closed immersion is faithful. -/
@[stacks 04CA, instance]
theorem smallEtalePushforward_closedImmersion_type_faithful :
    (Scheme.smallEtaleDirectImage.{u, u} i).Faithful := sorry

/-- The essential image of small-étale set-valued direct image along a closed immersion
consists of sheaves whose restriction to the complement is isomorphic to the terminal sheaf. -/
@[stacks 04CA]
theorem mem_essImage_smallEtalePushforward_closedImmersion_type_iff
    [HasWeakSheafify (closedImmersionComplement i).toScheme.smallEtaleTopology (Type u)]
    [∀ P : X.Etaleᵒᵖ ⥤ Type u,
      (Scheme.smallEtalePullback (closedImmersionComplement i).ι).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    (Scheme.smallEtaleDirectImage.{u, u} i).essImage F ↔
      restrictsToTerminalOnComplement i F := sorry

/-- The canonical counit of small-étale inverse image and direct image for sheaves of
sets along a closed immersion is invertible. -/
@[stacks 04CA, instance]
theorem isIso_counit_smallEtalePushforward_closedImmersion_type
    [HasWeakSheafify Z.smallEtaleTopology (Type u)]
    [∀ P : X.Etaleᵒᵖ ⥤ Type u, (Scheme.smallEtalePullback i).op.HasLeftKanExtension P] :
    IsIso ((Scheme.smallEtalePullback i).sheafAdjunctionContinuous
      (Type u) X.smallEtaleTopology Z.smallEtaleTopology).counit := sorry

/-- Small-étale direct image of abelian sheaves along a closed immersion is full. -/
@[stacks 04CA, instance]
theorem smallEtalePushforward_closedImmersion_ab_full :
    ((Scheme.smallEtalePullback i).sheafPushforwardContinuous
      AddCommGrpCat.{u} X.smallEtaleTopology Z.smallEtaleTopology).Full := sorry

/-- Small-étale direct image of abelian sheaves along a closed immersion is faithful. -/
@[stacks 04CA, instance]
theorem smallEtalePushforward_closedImmersion_ab_faithful :
    ((Scheme.smallEtalePullback i).sheafPushforwardContinuous
      AddCommGrpCat.{u} X.smallEtaleTopology Z.smallEtaleTopology).Faithful := sorry

/-- The essential image of small-étale abelian direct image along a closed immersion
consists of abelian sheaves whose support is contained in the closed image. -/
@[stacks 04CA]
theorem mem_essImage_smallEtalePushforward_closedImmersion_ab_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((Scheme.smallEtalePullback i).sheafPushforwardContinuous
      AddCommGrpCat.{u} X.smallEtaleTopology Z.smallEtaleTopology).essImage F ↔
      abelianSheafSupport F ⊆ Set.range i.base := sorry

/-- The canonical counit of small-étale inverse image and direct image for abelian
sheaves along a closed immersion is invertible. -/
@[stacks 04CA, instance]
theorem isIso_counit_smallEtalePushforward_closedImmersion_ab
    [HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (Scheme.smallEtalePullback i).op.HasLeftKanExtension P] :
    IsIso ((Scheme.smallEtalePullback i).sheafAdjunctionContinuous
      AddCommGrpCat.{u} X.smallEtaleTopology Z.smallEtaleTopology).counit := sorry

end AlgebraicGeometry.Scheme.Etale
