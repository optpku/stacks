/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import ReasLib.CategoryTheory.Adjunction.EpiMono
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally surjective morphisms of sheaves

This leaf provides functorial and pullback API for local surjectivity of
`Type`-valued sheaves.  It is deliberately separate from any particular
morphism-of-topoi presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uC uD uE uA vC vD vE vA wJ wK wM wA

namespace CategoryTheory

namespace Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- A functor between categories of type-valued sheaves preserves locally
surjective morphisms.  The source witness is an explicit argument so the API
can be used without introducing a local instance. -/
class PreservesLocallySurjective
    (F : Sheaf J (Type wJ) ⥤ Sheaf K (Type wK)) : Prop where
  /-- Locally surjective maps remain locally surjective after applying `F`. -/
  map {X Y : Sheaf J (Type wJ)} (f : X ⟶ Y) :
    Sheaf.IsLocallySurjective f → Sheaf.IsLocallySurjective (F.map f)

/-- Apply a functorial local-surjectivity preservation witness to an explicit
locally surjective map. -/
theorem map_isLocallySurjective
    (F : Sheaf J (Type wJ) ⥤ Sheaf K (Type wK))
    (hF : F.PreservesLocallySurjective)
    {X Y : Sheaf J (Type wJ)} (f : X ⟶ Y)
    (hf : Sheaf.IsLocallySurjective f) :
    Sheaf.IsLocallySurjective (F.map f) := sorry

/-- Typeclass-facing local-surjectivity preservation for a mapped sheaf
morphism. -/
instance map_isLocallySurjective_of_preservesLocallySurjective
    (F : Sheaf J (Type wJ) ⥤ Sheaf K (Type wK))
    [F.PreservesLocallySurjective]
    {X Y : Sheaf J (Type wJ)} (f : X ⟶ Y)
    [Sheaf.IsLocallySurjective f] :
    Sheaf.IsLocallySurjective (F.map f) := sorry

/-- Composite functors preserve locally surjective morphisms when each factor
does. -/
instance preservesLocallySurjective_comp
    {E : Type uE} [Category.{vE} E] {M : GrothendieckTopology E}
    (F : Sheaf J (Type wJ) ⥤ Sheaf K (Type wK))
    (G : Sheaf K (Type wK) ⥤ Sheaf M (Type wM))
    [F.PreservesLocallySurjective] [G.PreservesLocallySurjective] :
    (F ⋙ G).PreservesLocallySurjective := sorry

/-- On type-valued sheaves, preserving epimorphisms is equivalent to
preserving locally surjective morphisms once both sheaf categories have
sheafification. -/
theorem preservesEpimorphisms_iff_preservesLocallySurjective
    (F : Sheaf J (Type wJ) ⥤ Sheaf K (Type wK))
    [HasSheafify J (Type wJ)] [HasSheafify K (Type wK)] :
    F.PreservesEpimorphisms ↔ F.PreservesLocallySurjective := sorry

/-- A functor between type-valued sheaf categories which preserves pushouts
preserves locally surjective morphisms when its target has sheafification. -/
theorem preservesLocallySurjective_of_preservesPushouts
    (F : Sheaf J (Type wJ) ⥤ Sheaf K (Type wK))
    [HasSheafify K (Type wK)]
    (h_pushouts : PreservesColimitsOfShape WalkingSpan F) :
    F.PreservesLocallySurjective := sorry

/-- A functor between type-valued sheaf categories which preserves
coequalizers preserves locally surjective morphisms when its target has
sheafification. -/
theorem preservesLocallySurjective_of_preservesCoequalizers
    (F : Sheaf J (Type wJ) ⥤ Sheaf K (Type wK))
    [HasSheafify K (Type wK)]
    (h_coequalizers : PreservesColimitsOfShape WalkingParallelPair F) :
    F.PreservesLocallySurjective := sorry

end Functor

namespace Adjunction

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {L : Sheaf J (Type wJ) ⥤ Sheaf K (Type wK)}
variable {R : Sheaf K (Type wK) ⥤ Sheaf J (Type wJ)}

/-- For an adjunction between type-valued sheaf categories, locally
surjective counit components are equivalent to the right adjoint reflecting
epimorphisms.  No left-exactness hypothesis is needed. -/
theorem counit_isLocallySurjective_iff_reflectsEpimorphisms
    (adj : L ⊣ R)
    [HasSheafify K (Type wK)] :
    (∀ F : Sheaf K (Type wK), Sheaf.IsLocallySurjective (adj.counit.app F)) ↔
      R.ReflectsEpimorphisms := sorry

end Adjunction

namespace Sheaf

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}

/-- The second projection of a pullback of a locally surjective morphism of
type-valued sheaves is locally surjective. -/
theorem isLocallySurjective_pullback_snd
    {A B Z : Sheaf J (Type wJ)} (f : A ⟶ Z) (g : B ⟶ Z)
    (hf : IsLocallySurjective f) :
    IsLocallySurjective (pullback.snd f g) := sorry

/-- Typeclass-facing form of `isLocallySurjective_pullback_snd`. -/
instance pullback_snd_isLocallySurjective
    {A B Z : Sheaf J (Type wJ)} (f : A ⟶ Z) (g : B ⟶ Z)
    [IsLocallySurjective f] :
    IsLocallySurjective (pullback.snd f g) := sorry

section KernelPair

variable {F G : Sheaf J (Type wJ)} {φ : F ⟶ G}

/-- An explicitly locally surjective morphism of type-valued sheaves carries
explicit effective-epimorphism evidence in a regular-epi sheaf category. This
is not an instance. -/
theorem IsLocallySurjective.effectiveEpi
    [IsRegularEpiCategory (Sheaf J (Type wJ))]
    (hφ : IsLocallySurjective φ) :
    EffectiveEpi φ := sorry

/-- The kernel-pair cofork of an explicitly locally surjective morphism of
type-valued sheaves is a coequalizer in a regular-epi sheaf category. -/
noncomputable def IsLocallySurjective.isColimitCofork
    [IsRegularEpiCategory (Sheaf J (Type wJ))]
    (hφ : IsLocallySurjective φ) :
    IsColimit (Cofork.ofπ φ pullback.condition) :=
  @isColimitCoforkOfEffectiveEpi _ _ _ _ φ
    ((@regularEpiOfEpi _ _ _ _ _ φ
      (@epi_of_isLocallySurjective' _ _ _ _ _ φ hφ)).effectiveEpi)
    (pullback.cone φ φ) (pullback.isLimit φ φ)

end KernelPair

section CoefficientForget

variable {A : Type uA} [Category.{vA} A]
variable {FA : A → A → Type*} {CA : A → Type wA}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{wA} A FA]

/-- Forgetting the coefficients of a locally surjective sheaf morphism preserves local
surjectivity. -/
@[stacks 04DB "coefficient forgetting"]
theorem isLocallySurjective_sheafCompose_map
    [J.HasSheafCompose (forget A)]
    {X Y : Sheaf J A} (f : X ⟶ Y)
    (hf : IsLocallySurjective f) :
    IsLocallySurjective ((sheafCompose J (forget A)).map f) := sorry

/-- The canonical coefficient-forgetting functor on sheaves preserves epimorphisms whenever
epimorphisms are detected by local surjectivity. -/
@[stacks 04DB "forgetful epimorphisms"]
noncomputable instance sheafCompose_preservesEpimorphisms
    [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]
    [J.WEqualsLocallyBijective A] [HasSheafify J A]
    [J.HasSheafCompose (forget A)] [Balanced (Sheaf J A)] :
    (sheafCompose J (forget A)).PreservesEpimorphisms := sorry

end CoefficientForget

end Sheaf

end CategoryTheory
