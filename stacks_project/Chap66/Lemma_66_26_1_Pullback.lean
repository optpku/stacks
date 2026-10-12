/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Lemma_66_18_12_Restriction

/-!
# Étale pullback of modules on algebraic spaces

For an étale morphism `f : X ⟶ Y` of algebraic spaces, the inverse image of the structure
sheaf is an isomorphism, module pullback agrees with small étale inverse image on underlying
sheaves, and therefore `f^* : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` is exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Sheaf.InternalModule

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The inverse-image structure map of an étale morphism of algebraic spaces is an
isomorphism, so `f_small⁻¹ 𝒪_Y = 𝒪_X`. -/
instance ringedToposHom_structureMap_isIso (f : X ⟶ Y) [Etale f] :
    IsIso (ringedToposHom f).structureMap :=
  sorry

namespace Modules

/-- The identification `f^* 𝒢 = f_small⁻¹ 𝒢` on underlying sheaves, for an étale morphism of
algebraic spaces. -/
def pullbackIsoInverseImage (f : X ⟶ Y) [Etale f] :
    pullback f ⋙ ToInternal.underlying (structureSheaf X) ≅
      ToInternal.underlying (structureSheaf Y) ⋙ etaleRestrictionSheaf f (Type u) :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback f).symm
      (ToInternal.underlying (structureSheaf X)) ≪≫
    restrictFunctorIsoInverseImage f

/-- Objectwise, module pullback along an étale morphism agrees with étale restriction of the
underlying sheaf. -/
theorem pullbackIsoInverseImage_app (f : X ⟶ Y) [Etale f] (𝒢 : Y.Modules) :
    (pullbackIsoInverseImage f).app 𝒢 =
      (ToInternal.underlying (structureSheaf X)).mapIso
          ((restrictFunctorIsoPullback f).symm.app 𝒢) ≪≫
        (restrictFunctorIsoInverseImage f).app 𝒢 :=
  sorry

/-- `pullbackIsoInverseImage` is the Restrict identification of pullback with restriction,
composed with the identification of restriction with étale inverse image. -/
theorem pullbackIsoInverseImage_spec (f : X ⟶ Y) [Etale f] :
    pullbackIsoInverseImage f =
      Functor.isoWhiskerRight (restrictFunctorIsoPullback f).symm
          (ToInternal.underlying (structureSheaf X)) ≪≫
        restrictFunctorIsoInverseImage f :=
  sorry

/-- Pullback of sheaves of modules along an étale morphism of algebraic spaces is an exact
functor. -/
theorem pullback_exact (f : X ⟶ Y) [Etale f] :
    exactFunctor Y.Modules X.Modules (pullback f) :=
  sorry

/-- Étale module pullback preserves finite limits. -/
instance pullback_preservesFiniteLimits (f : X ⟶ Y) [Etale f] :
    PreservesFiniteLimits (pullback f) :=
  sorry

/-- Étale module pullback preserves finite colimits. -/
instance pullback_preservesFiniteColimits (f : X ⟶ Y) [Etale f] :
    PreservesFiniteColimits (pullback f) :=
  sorry

/-- Exactness of étale module pullback is equivalent to preservation of finite limits and
finite colimits. -/
theorem pullback_exact_iff (f : X ⟶ Y) [Etale f] :
    exactFunctor Y.Modules X.Modules (pullback f) ↔
      PreservesFiniteLimits (pullback f) ∧ PreservesFiniteColimits (pullback f) :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
