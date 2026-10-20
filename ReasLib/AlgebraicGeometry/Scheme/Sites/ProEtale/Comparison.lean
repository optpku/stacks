/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

/-!
# Small-to-big pro-étale comparison on abelian sheaves

The morphism of sites `π_S` induced by `ProEt.forget` has abelian inverse image
`π_S⁻¹`, direct image `π_{S,*} = i_S⁻¹`, and unbounded derived adjunction
`π_S⁻¹ ⊣ Rπ_{S,*}`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

section

variable (S : Scheme.{u})

/-- The small-to-big inclusion `ProEt.forget` is cocontinuous for the small and big
pro-étale topologies. -/
instance forget_isCocontinuous :
    (ProEt.forget S).IsCocontinuous (topology S) (proetaleTopology.over S) := sorry

/-- The small-to-big inclusion `ProEt.forget` is a morphism of sites from the big
pro-étale slice to the small pro-étale site. -/
instance forget_isMorphismOfSites :
    IsMorphismOfSites (topology S) (proetaleTopology.over S) (ProEt.forget S) :=
  inferInstance

variable [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
variable [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
variable [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (ProEt.forget S).op.HasLeftKanExtension P]

/-- Inverse image `π_S⁻¹` on abelian sheaves along the small-to-big pro-étale inclusion. -/
abbrev piInverseImage :
    Sheaf (topology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1} :=
  (ProEt.forget S).sheafPullback AddCommGrpCat.{u + 1}
    (topology S) (proetaleTopology.over S)

/-- Inverse image `π_S⁻¹` is sheaf pullback along `ProEt.forget`. -/
theorem piInverseImage_eq :
    piInverseImage S =
      (ProEt.forget S).sheafPullback AddCommGrpCat.{u + 1}
        (topology S) (proetaleTopology.over S) := sorry

/-- Direct image `π_{S,*}` on abelian sheaves, equal to restriction `i_S⁻¹` along the
small-to-big inclusion. -/
abbrev piPushforward :
    Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology S) AddCommGrpCat.{u + 1} :=
  (ProEt.forget S).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (topology S) (proetaleTopology.over S)

/-- Direct image `π_{S,*}` is continuous sheaf pushforward along `ProEt.forget`. -/
theorem piPushforward_eq :
    piPushforward S =
      (ProEt.forget S).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (topology S) (proetaleTopology.over S) := sorry

/-- Sheaf-level adjunction `π_S⁻¹ ⊣ π_{S,*}`. -/
def piAdjunction : piInverseImage S ⊣ piPushforward S :=
  (ProEt.forget S).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (topology S) (proetaleTopology.over S)

/-- The sheaf-level adjunction `π_S⁻¹ ⊣ π_{S,*}` is the continuous sheaf adjunction
along `ProEt.forget`. -/
theorem piAdjunction_eq :
    piAdjunction S =
      (ProEt.forget S).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (topology S) (proetaleTopology.over S) := sorry

/-- Inverse image `π_S⁻¹` preserves finite limits. -/
instance piInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (piInverseImage S) := sorry

/-- Inverse image `π_S⁻¹` preserves finite colimits. -/
instance piInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (piInverseImage S) := sorry

/-- Direct image `π_{S,*}` is additive. -/
instance piPushforward_additive : (piPushforward S).Additive :=
  inferInstance

/-- Exact inverse image `π_S⁻¹` on abelian sheaves. -/
abbrev piExact :
    Sheaf (topology S) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (piInverseImage S)

/-- Exact inverse image `π_S⁻¹` is the bundled exact functor of `piInverseImage`. -/
theorem piExact_eq :
    piExact S = ExactFunctor.of (piInverseImage S) := sorry

/-- The sheaf-level adjunction unit of `π_S⁻¹ ⊣ π_{S,*}` is an isomorphism on every
abelian sheaf. This is the identity-composition `π_{S,*} ∘ π_S⁻¹ ≅ 𝟭`. -/
instance piAdjunction_unit_app_isIso
    (F : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    IsIso ((piAdjunction S).unit.app F) := sorry

/-- The sheaf-level adjunction unit of `π_S⁻¹ ⊣ π_{S,*}` is an isomorphism. -/
instance piAdjunction_unit_isIso : IsIso (piAdjunction S).unit := sorry

/-- Unbounded derived adjunction `π_S⁻¹ ⊣ Rπ_{S,*}` on abelian pro-étale sheaves. -/
def piDerivedAdjunction :
    Adjunction.Derived.KInjective.left (piExact S) ⊣
      Adjunction.Derived.KInjective.right (piPushforward S) :=
  Adjunction.Derived.KInjective.adjunction (piExact S) (piPushforward S)
    (piAdjunction S)

/-- The unbounded derived adjunction is the K-injective derived adjunction of
`π_S⁻¹ ⊣ π_{S,*}`. -/
theorem piDerivedAdjunction_eq :
    piDerivedAdjunction S =
      Adjunction.Derived.KInjective.adjunction (piExact S) (piPushforward S)
        (piAdjunction S) := sorry

end

/-- For every scheme `S` and derived abelian sheaf `K` on its small pro-étale site,
the canonical unit `K ⟶ Rπ_{S,*}(π_S⁻¹ K)` is an isomorphism. -/
theorem piDerivedAdjunction_unit_isIso (S : Scheme.{u})
    (K : DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1})) :
    IsIso ((piDerivedAdjunction S).unit.app K) := sorry

end AlgebraicGeometry.Scheme.ProEt
