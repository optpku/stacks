module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of localization lower shriek for module sheaves

This file records the finite-limit and finite-colimit preservation API for extension from a
slice site.  The construction is the canonical presheaf-module pullback followed by ambient
sheafification from `SheafOfModules.Localization`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w z

namespace SheafOfModules.Localization

section AbstractAdjunction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{w}) (U : C)
variable [(restriction R U : SheafOfModules.{z} R ⥤
  SheafOfModules.{z} (R.over U)).IsRightAdjoint]

/-- Exactness of extension from a slice depends only on the existence of the localization
adjunction; construction-specific sheafification hypotheses are not part of its reusable API. -/
@[stacks 03DJ "exactness from the localization adjunction"]
theorem lowerShriek.exactOfIsRightAdjoint :
    exactFunctor
      (SheafOfModules.{z} (R.over U)) (SheafOfModules.{z} R)
      (lowerShriek R U) := sorry

end AbstractAdjunction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{w}) (U : C)
variable [presheafRestrictionIsRightAdjoint :
  ((PresheafOfModules.pushforward (restrictionRingHom R U).hom) :
    PresheafOfModules.{z} R.obj ⥤ PresheafOfModules.{z} (R.over U).obj).IsRightAdjoint]
variable [HasSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]

namespace lowerShriek

/-- Extension of module sheaves from a slice site is additive. -/
@[stacks 03DJ "additivity"]
instance additive :
    (lowerShriek R U :
      SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R).Additive := sorry

/-- Extension of module sheaves from a slice site preserves finite limits. -/
@[stacks 03DJ "finite-limit preservation"]
instance preservesFiniteLimits :
    PreservesFiniteLimits
      (lowerShriek R U :
        SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R) := sorry

/-- Extension of module sheaves from a slice site preserves finite colimits. -/
@[stacks 03DJ "finite-colimit preservation"]
instance preservesFiniteColimits :
    PreservesFiniteColimits
      (lowerShriek R U :
        SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R) := sorry

/-- Extension of module sheaves from a slice localization is exact. -/
@[stacks 03DJ]
theorem exact :
    exactFunctor
      (SheafOfModules.{z} (R.over U)) (SheafOfModules.{z} R)
      (lowerShriek R U) := sorry

/-- Extension of module sheaves from a slice site preserves monomorphisms. -/
@[stacks 03DJ "monomorphism preservation"]
instance preservesMonomorphisms :
    (lowerShriek R U :
      SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R).PreservesMonomorphisms := sorry

/-- Extension of module sheaves from a slice site preserves epimorphisms. -/
@[stacks 03DJ "epimorphism preservation"]
instance preservesEpimorphisms :
    (lowerShriek R U :
      SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R).PreservesEpimorphisms := sorry

/-- Extension of module sheaves from a slice site is faithful. -/
@[stacks 0E8G "faithfulness"]
instance faithful :
    (lowerShriek R U :
      SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R).Faithful := sorry

/-- Extension from a slice site maps exact short complexes to exact short complexes. -/
@[stacks 0E8G "preservation of exact short complexes"]
theorem mapExact (S : ShortComplex (SheafOfModules.{z} (R.over U)))
    (hS : S.Exact) :
    (S.map (lowerShriek R U :
      SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R)).Exact := sorry

/-- Faithful extension from a slice site reflects exactness of short complexes. -/
@[stacks 0E8G "reflection of exact short complexes"]
theorem reflectsExact (S : ShortComplex (SheafOfModules.{z} (R.over U)))
    (hS : (S.map (lowerShriek R U :
      SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R)).Exact) :
    S.Exact := sorry

/-- A short complex on the slice site is exact if and only if its extension to the ambient site
is exact. -/
@[stacks 0E8G]
theorem exactMapIff (S : ShortComplex (SheafOfModules.{z} (R.over U))) :
    S.Exact ↔
      (S.map (lowerShriek R U :
        SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R)).Exact := sorry

end lowerShriek

end SheafOfModules.Localization
