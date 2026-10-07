module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_6_2_RingedTopos
public import stacks_project.Chap103.Lemma_103_9_2

/-!
# Vanishing and pushforward of parasitic modules on algebraic stacks

For `τ` étale or fppf, a parasitic object of `Mod(X_τ, 𝒪_X)` has vanishing
`τ`-cohomology, and its higher direct images along any morphism of algebraic
stacks remain parasitic.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Module direct image along `associatedRingedToposHom f τ` is additive. -/
instance associatedRingedToposHom_modulePushforward_additive
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology) :
    ((associatedRingedToposHom f τ).modulePushforward).Additive :=
  RingedSite.ToposHom.modulePushforward_additive (associatedRingedToposHom f τ)

/-- The degree-`i` higher direct image `R^i f_* F` of an associated `τ`-module,
computed in the `τ`-topology. -/
abbrev associatedModules.higherDirectImage {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (τ : StandardTopology) (F : associatedModules X τ) (i : ℕ)
    [HasInjectiveResolutions (associatedModules X τ)] :
    associatedModules Y τ :=
  ((associatedRingedToposHom f τ).modulePushforward.rightDerived i).obj F

/-- `associatedModules.higherDirectImage f τ F i` is the object map of the
degree-`i` right derived functor of module direct image along
`associatedRingedToposHom f τ`. -/
theorem associatedModules.higherDirectImage_eq {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (τ : StandardTopology) (F : associatedModules X τ) (i : ℕ)
    [HasInjectiveResolutions (associatedModules X τ)] :
    associatedModules.higherDirectImage f τ F i =
      ((associatedRingedToposHom f τ).modulePushforward.rightDerived i).obj F :=
  sorry

/-- Lemma 103.9.3 (1): if `τ` is étale or fppf, `X` is an algebraic stack, and
`F` is a parasitic object of `Mod(X_τ, 𝒪_X)`, then
`H^i_τ(X, F)` vanishes for every `i`. -/
@[stacks 0775]
theorem isZero_cohomology_of_isParasitic {X : GroupoidsOver S} [AlgebraicStack X]
    {τ : StandardTopology} (hτ : τ = .etale ∨ τ = .fppf)
    (F : associatedModules X τ) [IsParasitic (associatedModulePresheaf F)]
    (i : ℕ) [HasExt (associatedModules X τ)] :
    IsZero (RingedSite.Hom.moduleGlobalCohomology (associatedRingedSite X τ) F i) :=
  sorry

/-- Lemma 103.9.3 (2): if `τ` is étale or fppf, `f : X ⟶ Y` is a morphism of
algebraic stacks, and `F` is a parasitic object of `Mod(X_τ, 𝒪_X)`, then
`R^i f_* F`, computed in the `τ`-topology, is a parasitic object of
`Mod(Y_τ, 𝒪_Y)`. -/
@[stacks 0775]
theorem associatedModules.isParasitic_higherDirectImage
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {τ : StandardTopology} (hτ : τ = .etale ∨ τ = .fppf) (f : X ⟶ Y)
    (F : associatedModules X τ) [IsParasitic (associatedModulePresheaf F)] (i : ℕ)
    [HasInjectiveResolutions (associatedModules X τ)] :
    IsParasitic
      (associatedModulePresheaf (associatedModules.higherDirectImage f τ F i)) :=
  sorry

/-- Parasitic higher direct images remain parasitic in the étale topology. -/
instance associatedModules.instParasitic_higherDirectImage_etale
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (F : associatedModules X .etale)
    [IsParasitic (associatedModulePresheaf F)] (i : ℕ)
    [HasInjectiveResolutions (associatedModules X .etale)] :
    IsParasitic
      (associatedModulePresheaf
        (associatedModules.higherDirectImage f .etale F i)) :=
  associatedModules.isParasitic_higherDirectImage (Or.inl rfl) f F i

/-- Parasitic higher direct images remain parasitic in the fppf topology. -/
instance associatedModules.instParasitic_higherDirectImage_fppf
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (F : associatedModules X .fppf)
    [IsParasitic (associatedModulePresheaf F)] (i : ℕ)
    [HasInjectiveResolutions (associatedModules X .fppf)] :
    IsParasitic
      (associatedModulePresheaf
        (associatedModules.higherDirectImage f .fppf F i)) :=
  associatedModules.isParasitic_higherDirectImage (Or.inr rfl) f F i

end AlgebraicGeometry.GroupoidsOver
