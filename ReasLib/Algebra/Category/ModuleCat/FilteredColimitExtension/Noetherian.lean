/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

namespace ModuleCat

/-- A functor between finitely generated module categories over Noetherian rings has a
filtered-colimit-preserving extension to all modules, unique up to a unique natural
isomorphism compatible with the specified restriction isomorphisms. -/
theorem fgFilteredColimitExtension_existsUnique
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [CommRing B] [IsNoetherianRing B]
    (F : FGModuleCat.{max u v} A ⥤ FGModuleCat.{max u v} B) :
    ∃ (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
      (eF' : (isFG.{max u v} A).ι ⋙ F' ≅ F ⋙ (isFG.{max u v} B).ι)
      (_ : PreservesFilteredColimitsOfSize.{max u v, max u v} F'),
      ∀ (G : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
        (eG : (isFG.{max u v} A).ι ⋙ G ≅ F ⋙ (isFG.{max u v} B).ι),
        PreservesFilteredColimitsOfSize.{max u v, max u v} G →
          ∃! α : F' ≅ G,
            Functor.isoWhiskerLeft (isFG.{max u v} A).ι α ≪≫ eG = eF' := sorry

/-- A filtered-colimit-preserving extension of an additive functor between finitely
generated module categories over Noetherian rings is additive. -/
theorem fgFilteredColimitExtension_additive
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [CommRing B] [IsNoetherianRing B]
    (F : FGModuleCat.{max u v} A ⥤ FGModuleCat.{max u v} B)
    [F.Additive]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFG.{max u v} A).ι ⋙ F' ≅ F ⋙ (isFG.{max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F'] :
    F'.Additive := sorry

/-- A filtered-colimit-preserving extension of an additive functor between finitely
generated module categories over Noetherian rings preserves coproducts indexed by any
type in the module universe. -/
theorem fgFilteredColimitExtension_preservesCoproducts
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [CommRing B] [IsNoetherianRing B]
    (F : FGModuleCat.{max u v} A ⥤ FGModuleCat.{max u v} B)
    [F.Additive]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFG.{max u v} A).ι ⋙ F' ≅ F ⋙ (isFG.{max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (J : Type (max u v)) :
    PreservesColimitsOfShape (Discrete J) F' := sorry

/-- A filtered-colimit-preserving extension of a finite-colimit-preserving functor between
finitely generated module categories over Noetherian rings preserves finite colimits. -/
theorem fgFilteredColimitExtension_preservesFiniteColimits
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [CommRing B] [IsNoetherianRing B]
    (F : FGModuleCat.{max u v} A ⥤ FGModuleCat.{max u v} B)
    [PreservesFiniteColimits F]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFG.{max u v} A).ι ⋙ F' ≅ F ⋙ (isFG.{max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F'] :
    PreservesFiniteColimits F' := sorry

/-- A filtered-colimit-preserving extension of a finite-limit-preserving functor between
finitely generated module categories over Noetherian rings preserves finite limits. -/
theorem fgFilteredColimitExtension_preservesFiniteLimits
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [CommRing B] [IsNoetherianRing B]
    (F : FGModuleCat.{max u v} A ⥤ FGModuleCat.{max u v} B)
    [PreservesFiniteLimits F]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFG.{max u v} A).ι ⋙ F' ≅ F ⋙ (isFG.{max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F'] :
    PreservesFiniteLimits F' := sorry

end ModuleCat
