/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Composition
public import ReasLib.CategoryTheory.Adjunction.BaseChange.HorizontalComposition

@[expose] public section

/-!
# Horizontal composition of derived base-change maps on ringed sites

The generic adjunction-mate composition API specializes to the canonical derived module
pullback-pushforward adjunctions. The outer namespace allows chosen pullback-composition
isomorphisms; `Canonical` fixes them to the standard derived-pullback comparisons.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe z uX₀ vX₀ uX₁ vX₁ uX₂ vX₂ uY₀ vY₀ uY₁ vY₁ uY₂ vY₂ w

namespace RingedSite.Hom.DerivedBaseChange.HorizontalComposition

section

variable {X₀ : RingedSite.{uX₀, vX₀, w}} {X₁ : RingedSite.{uX₁, vX₁, w}}
variable {X₂ : RingedSite.{uX₂, vX₂, w}} {Y₀ : RingedSite.{uY₀, vY₀, w}}
variable {Y₁ : RingedSite.{uY₁, vY₁, w}} {Y₂ : RingedSite.{uY₂, vY₂, w}}
variable (g₁ : RingedSite.Hom X₂ X₁) (g₀ : RingedSite.Hom X₁ X₀)
variable (f₂ : RingedSite.Hom X₂ Y₂) (f₁ : RingedSite.Hom X₁ Y₁)
variable (f₀ : RingedSite.Hom X₀ Y₀) (h₁ : RingedSite.Hom Y₂ Y₁)
variable (h₀ : RingedSite.Hom Y₁ Y₀)
variable [UnivLE.{max uX₀ vX₀, z}] [UnivLE.{max uX₁ vX₁, z}]
variable [UnivLE.{max uX₂ vX₂, z}] [UnivLE.{max uY₀ vY₀, z}]
variable [UnivLE.{max uY₁ vY₁, z}] [UnivLE.{max uY₂ vY₂, z}]
variable [(g₁.modulePushforward.{z}).IsRightAdjoint]
variable [(g₀.modulePushforward.{z}).IsRightAdjoint]
variable [(f₂.modulePushforward.{z}).IsRightAdjoint]
variable [(f₁.modulePushforward.{z}).IsRightAdjoint]
variable [(f₀.modulePushforward.{z}).IsRightAdjoint]
variable [(h₁.modulePushforward.{z}).IsRightAdjoint]
variable [(h₀.modulePushforward.{z}).IsRightAdjoint]
variable [((g₁.comp g₀).modulePushforward.{z}).IsRightAdjoint]
variable [((h₁.comp h₀).modulePushforward.{z}).IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f₂) (ModuleQis.{z} X₂)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f₁) (ModuleQis.{z} X₁)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f₀) (ModuleQis.{z} X₀)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} g₁) (ModuleQis.{z} X₁)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} g₀) (ModuleQis.{z} X₀)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f₂) (ModuleQis.{z} Y₂)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f₁) (ModuleQis.{z} Y₁)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f₀) (ModuleQis.{z} Y₀)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} h₁) (ModuleQis.{z} Y₁)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} h₀) (ModuleQis.{z} Y₀)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} (g₁.comp g₀)) (ModuleQis.{z} X₀)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} (h₁.comp h₀)) (ModuleQis.{z} Y₀)]
variable [DerivedAdjunction.HasPair.{z} f₂]
variable [DerivedAdjunction.HasPair.{z} f₁]
variable [DerivedAdjunction.HasPair.{z} f₀]

/-- The derived-pullback square for the outer rectangle obtained by horizontally pasting two
squares and transporting the two horizontal composites along chosen isomorphisms. -/
@[stacks 0E47 "horizontally pasted derived-pullback square"]
noncomputable abbrev squareIso
    (square₀ : modulePullbackDerived.{z} h₀ ⋙ modulePullbackDerived.{z} f₁ ≅
      modulePullbackDerived.{z} f₀ ⋙ modulePullbackDerived.{z} g₀)
    (square₁ : modulePullbackDerived.{z} h₁ ⋙ modulePullbackDerived.{z} f₂ ≅
      modulePullbackDerived.{z} f₁ ⋙ modulePullbackDerived.{z} g₁)
    (leftComp : modulePullbackDerived.{z} (h₁.comp h₀) ≅
      modulePullbackDerived.{z} h₀ ⋙ modulePullbackDerived.{z} h₁)
    (rightComp : modulePullbackDerived.{z} (g₁.comp g₀) ≅
      modulePullbackDerived.{z} g₀ ⋙ modulePullbackDerived.{z} g₁) :
    modulePullbackDerived.{z} (h₁.comp h₀) ⋙ modulePullbackDerived.{z} f₂ ≅
      modulePullbackDerived.{z} f₀ ⋙ modulePullbackDerived.{z} (g₁.comp g₀) :=
  CategoryTheory.DerivedBaseChange.HorizontalComposition.squareIso
    square₀ square₁ leftComp rightComp

/-- The horizontal composite of two chosen derived base-change morphisms, transported along
chosen pullback-composition isomorphisms. -/
@[stacks 0E47 "horizontal composite of unbounded base-change morphisms"]
noncomputable def map
    (leftComp : modulePullbackDerived.{z} (h₁.comp h₀) ≅
      modulePullbackDerived.{z} h₀ ⋙ modulePullbackDerived.{z} h₁)
    (rightComp : modulePullbackDerived.{z} (g₁.comp g₀) ≅
      modulePullbackDerived.{z} g₀ ⋙ modulePullbackDerived.{z} g₁)
    (K : ModuleDerived.{z} X₀)
    (η₀ : (modulePullbackDerived.{z} h₀).obj
        ((modulePushforwardDerived.{z} f₀).obj K) ⟶
      (modulePushforwardDerived.{z} f₁).obj
        ((modulePullbackDerived.{z} g₀).obj K))
    (η₁ : (modulePullbackDerived.{z} h₁).obj
        ((modulePushforwardDerived.{z} f₁).obj
          ((modulePullbackDerived.{z} g₀).obj K)) ⟶
      (modulePushforwardDerived.{z} f₂).obj
        ((modulePullbackDerived.{z} g₁).obj
          ((modulePullbackDerived.{z} g₀).obj K))) :
    (modulePullbackDerived.{z} (h₁.comp h₀)).obj
        ((modulePushforwardDerived.{z} f₀).obj K) ⟶
      (modulePushforwardDerived.{z} f₂).obj
        ((modulePullbackDerived.{z} (g₁.comp g₀)).obj K) :=
  CategoryTheory.DerivedBaseChange.HorizontalComposition.map
    leftComp rightComp K η₀ η₁

/-- Horizontal composition preserves the defining mate equation for derived base-change maps. -/
@[stacks 0E47 "horizontal composition of unbounded base-change maps"]
theorem map_isMap
    (square₀ : modulePullbackDerived.{z} h₀ ⋙ modulePullbackDerived.{z} f₁ ≅
      modulePullbackDerived.{z} f₀ ⋙ modulePullbackDerived.{z} g₀)
    (square₁ : modulePullbackDerived.{z} h₁ ⋙ modulePullbackDerived.{z} f₂ ≅
      modulePullbackDerived.{z} f₁ ⋙ modulePullbackDerived.{z} g₁)
    (leftComp : modulePullbackDerived.{z} (h₁.comp h₀) ≅
      modulePullbackDerived.{z} h₀ ⋙ modulePullbackDerived.{z} h₁)
    (rightComp : modulePullbackDerived.{z} (g₁.comp g₀) ≅
      modulePullbackDerived.{z} g₀ ⋙ modulePullbackDerived.{z} g₁)
    (K : ModuleDerived.{z} X₀)
    (η₀ : (modulePullbackDerived.{z} h₀).obj
        ((modulePushforwardDerived.{z} f₀).obj K) ⟶
      (modulePushforwardDerived.{z} f₁).obj
        ((modulePullbackDerived.{z} g₀).obj K))
    (η₁ : (modulePullbackDerived.{z} h₁).obj
        ((modulePushforwardDerived.{z} f₁).obj
          ((modulePullbackDerived.{z} g₀).obj K)) ⟶
      (modulePushforwardDerived.{z} f₂).obj
        ((modulePullbackDerived.{z} g₁).obj
          ((modulePullbackDerived.{z} g₀).obj K)))
    (hη₀ : DerivedBaseChange.IsMap g₀ f₁ f₀ h₀ square₀ K η₀)
    (hη₁ : DerivedBaseChange.IsMap g₁ f₂ f₁ h₁ square₁
      ((modulePullbackDerived.{z} g₀).obj K) η₁) :
    DerivedBaseChange.IsMap (g₁.comp g₀) f₂ f₀ (h₁.comp h₀)
      (squareIso g₁ g₀ f₂ f₁ f₀ h₁ h₀ square₀ square₁ leftComp rightComp) K
      (map g₁ g₀ f₂ f₁ f₀ h₁ h₀ leftComp rightComp K η₀ η₁) := sorry

/-- The horizontal composite of two canonical derived base-change maps is the canonical map of
the pasted square. -/
@[stacks 0E47 "canonical unbounded base-change maps compose horizontally"]
theorem map_eq
    (square₀ : modulePullbackDerived.{z} h₀ ⋙ modulePullbackDerived.{z} f₁ ≅
      modulePullbackDerived.{z} f₀ ⋙ modulePullbackDerived.{z} g₀)
    (square₁ : modulePullbackDerived.{z} h₁ ⋙ modulePullbackDerived.{z} f₂ ≅
      modulePullbackDerived.{z} f₁ ⋙ modulePullbackDerived.{z} g₁)
    (leftComp : modulePullbackDerived.{z} (h₁.comp h₀) ≅
      modulePullbackDerived.{z} h₀ ⋙ modulePullbackDerived.{z} h₁)
    (rightComp : modulePullbackDerived.{z} (g₁.comp g₀) ≅
      modulePullbackDerived.{z} g₀ ⋙ modulePullbackDerived.{z} g₁)
    (K : ModuleDerived.{z} X₀) :
    map g₁ g₀ f₂ f₁ f₀ h₁ h₀ leftComp rightComp K
        (DerivedBaseChange.map g₀ f₁ f₀ h₀ square₀ K)
        (DerivedBaseChange.map g₁ f₂ f₁ h₁ square₁
          ((modulePullbackDerived.{z} g₀).obj K)) =
      DerivedBaseChange.map (g₁.comp g₀) f₂ f₀ (h₁.comp h₀)
        (squareIso g₁ g₀ f₂ f₁ f₀ h₁ h₀ square₀ square₁ leftComp rightComp) K := sorry

namespace Canonical

variable [IsIso (modulePullbackDerived.compComparison g₁ g₀)]
variable [IsIso (modulePullbackDerived.compComparison h₁ h₀)]

/-- The canonical derived-pullback square for the outer rectangle, using the standard composition
comparisons for its two horizontal sides. -/
@[stacks 0E47 "canonical horizontally pasted derived-pullback square"]
noncomputable abbrev squareIso
    (square₀ : modulePullbackDerived.{z} h₀ ⋙ modulePullbackDerived.{z} f₁ ≅
      modulePullbackDerived.{z} f₀ ⋙ modulePullbackDerived.{z} g₀)
    (square₁ : modulePullbackDerived.{z} h₁ ⋙ modulePullbackDerived.{z} f₂ ≅
      modulePullbackDerived.{z} f₁ ⋙ modulePullbackDerived.{z} g₁) :
    modulePullbackDerived.{z} (h₁.comp h₀) ⋙ modulePullbackDerived.{z} f₂ ≅
      modulePullbackDerived.{z} f₀ ⋙ modulePullbackDerived.{z} (g₁.comp g₀) :=
  HorizontalComposition.squareIso g₁ g₀ f₂ f₁ f₀ h₁ h₀ square₀ square₁
    (modulePullbackDerived.compIso h₁ h₀).symm
    (modulePullbackDerived.compIso g₁ g₀).symm

/-- The canonical-comparison form of the horizontal composite of two chosen derived base-change
morphisms. -/
@[stacks 0E47 "canonical horizontal composite of unbounded base-change morphisms"]
noncomputable abbrev map
    (K : ModuleDerived.{z} X₀)
    (η₀ : (modulePullbackDerived.{z} h₀).obj
        ((modulePushforwardDerived.{z} f₀).obj K) ⟶
      (modulePushforwardDerived.{z} f₁).obj
        ((modulePullbackDerived.{z} g₀).obj K))
    (η₁ : (modulePullbackDerived.{z} h₁).obj
        ((modulePushforwardDerived.{z} f₁).obj
          ((modulePullbackDerived.{z} g₀).obj K)) ⟶
      (modulePushforwardDerived.{z} f₂).obj
        ((modulePullbackDerived.{z} g₁).obj
          ((modulePullbackDerived.{z} g₀).obj K))) :
    (modulePullbackDerived.{z} (h₁.comp h₀)).obj
        ((modulePushforwardDerived.{z} f₀).obj K) ⟶
      (modulePushforwardDerived.{z} f₂).obj
        ((modulePullbackDerived.{z} (g₁.comp g₀)).obj K) :=
  HorizontalComposition.map g₁ g₀ f₂ f₁ f₀ h₁ h₀
    (modulePullbackDerived.compIso h₁ h₀).symm
    (modulePullbackDerived.compIso g₁ g₀).symm K η₀ η₁

/-- Under the canonical pullback-composition comparisons, horizontal composition preserves the
derived base-change mate condition. -/
@[stacks 0E47 "canonical horizontal composition preserves base change"]
theorem map_isMap
    (square₀ : modulePullbackDerived.{z} h₀ ⋙ modulePullbackDerived.{z} f₁ ≅
      modulePullbackDerived.{z} f₀ ⋙ modulePullbackDerived.{z} g₀)
    (square₁ : modulePullbackDerived.{z} h₁ ⋙ modulePullbackDerived.{z} f₂ ≅
      modulePullbackDerived.{z} f₁ ⋙ modulePullbackDerived.{z} g₁)
    (K : ModuleDerived.{z} X₀)
    (η₀ : (modulePullbackDerived.{z} h₀).obj
        ((modulePushforwardDerived.{z} f₀).obj K) ⟶
      (modulePushforwardDerived.{z} f₁).obj
        ((modulePullbackDerived.{z} g₀).obj K))
    (η₁ : (modulePullbackDerived.{z} h₁).obj
        ((modulePushforwardDerived.{z} f₁).obj
          ((modulePullbackDerived.{z} g₀).obj K)) ⟶
      (modulePushforwardDerived.{z} f₂).obj
        ((modulePullbackDerived.{z} g₁).obj
          ((modulePullbackDerived.{z} g₀).obj K)))
    (hη₀ : DerivedBaseChange.IsMap g₀ f₁ f₀ h₀ square₀ K η₀)
    (hη₁ : DerivedBaseChange.IsMap g₁ f₂ f₁ h₁ square₁
      ((modulePullbackDerived.{z} g₀).obj K) η₁) :
    DerivedBaseChange.IsMap (g₁.comp g₀) f₂ f₀ (h₁.comp h₀)
      (squareIso g₁ g₀ f₂ f₁ f₀ h₁ h₀ square₀ square₁) K
      (map g₁ g₀ f₂ f₁ f₀ h₁ h₀ K η₀ η₁) := sorry

/-- Remark 21.19.5 (0E47): with the canonical pullback-composition comparisons, the two
canonical derived base-change maps compose to the canonical map for the outer rectangle. -/
@[stacks 0E47 "canonical horizontal base-change composition"]
theorem map_eq
    (square₀ : modulePullbackDerived.{z} h₀ ⋙ modulePullbackDerived.{z} f₁ ≅
      modulePullbackDerived.{z} f₀ ⋙ modulePullbackDerived.{z} g₀)
    (square₁ : modulePullbackDerived.{z} h₁ ⋙ modulePullbackDerived.{z} f₂ ≅
      modulePullbackDerived.{z} f₁ ⋙ modulePullbackDerived.{z} g₁)
    (K : ModuleDerived.{z} X₀) :
    map g₁ g₀ f₂ f₁ f₀ h₁ h₀ K
        (DerivedBaseChange.map g₀ f₁ f₀ h₀ square₀ K)
        (DerivedBaseChange.map g₁ f₂ f₁ h₁ square₁
          ((modulePullbackDerived.{z} g₀).obj K)) =
      DerivedBaseChange.map (g₁.comp g₀) f₂ f₀ (h₁.comp h₀)
        (squareIso g₁ g₀ f₂ f₁ f₀ h₁ h₀ square₀ square₁) K := sorry

end Canonical

end

end RingedSite.Hom.DerivedBaseChange.HorizontalComposition

-- The two map definitions are explicit specializations of the generic composite, while the
-- square data uses only supplied or canonical comparison isomorphisms.
