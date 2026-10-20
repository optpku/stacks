/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Homotopy.KInjective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.QuasiIso
public import ReasLib.CategoryTheory.Functor.Injective

/-!
# K-injective differential graded modules

This file supplies the module-level typeclass interface to the intrinsic homotopy-category
property `Homotopy.kInjective`.  It also packages functorial graded-injective K-injective
replacements without choosing one globally.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib intentionally keeps this construction non-global because a global instance breaks
-- sheaf/free elaboration.  This bridge must reuse the homotopy K-injective owner's choice.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Module

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {𝒜 : DGA(𝒪)}

/-- A DG module is K-injective when its represented object in the intrinsic DG homotopy
category is right orthogonal to all acyclic objects. -/
@[stacks 0FSU]
class IsKInjective (I : Mod(𝒜, d)) : Prop where
  /-- The represented DG module is K-injective in the homotopy category. -/
  mem : Homotopy.kInjective 𝒜 ((toK 𝒜).obj I)

namespace IsKInjective

/-- The module-level K-injective predicate is equivalent to its canonical homotopy-category
property. -/
theorem iff (I : Mod(𝒜, d)) :
    IsKInjective I ↔ Homotopy.kInjective 𝒜 ((toK 𝒜).obj I) := sorry

/-- A K-injective DG module is K-injective after passage to the homotopy category. -/
theorem homotopy_mem (I : Mod(𝒜, d)) [IsKInjective I] :
    Homotopy.kInjective 𝒜 ((toK 𝒜).obj I) := sorry

/-- Precomposition by a DG-module quasi-isomorphism is bijective on homotopy classes into a
K-injective target. -/
theorem precomp_bijective {M M' I : Mod(𝒜, d)}
    (b : M ⟶ M') (hb : quasiIso 𝒜 b) [IsKInjective I] :
    Function.Bijective
      (fun f : (toK 𝒜).obj M' ⟶ (toK 𝒜).obj I ↦
        (toK 𝒜).map b ≫ f) := sorry

/-- Every morphism into a K-injective target extends across a quasi-isomorphism, with the
extension triangle commuting in the intrinsic DG homotopy category. -/
@[stacks 0FSX]
theorem exists_lift {M M' I : Mod(𝒜, d)}
    (a : M ⟶ I) (b : M ⟶ M') (hb : quasiIso 𝒜 b)
    [IsKInjective I] :
    ∃ a' : M' ⟶ I,
      (toK 𝒜).map (b ≫ a') = (toK 𝒜).map a := sorry

/-- Two extensions into a K-injective target which agree after a quasi-isomorphism define the
same intrinsic homotopy class. -/
theorem lift_unique {M M' I : Mod(𝒜, d)}
    (b : M ⟶ M') (hb : quasiIso 𝒜 b) [IsKInjective I]
    {a' a'' : M' ⟶ I}
    (h : (toK 𝒜).map (b ≫ a') = (toK 𝒜).map (b ≫ a'')) :
    (toK 𝒜).map a' = (toK 𝒜).map a'' := sorry

/-- K-injectivity is invariant under isomorphism of DG modules. -/
theorem ofIso {I I' : Mod(𝒜, d)} (e : I ≅ I') [IsKInjective I] :
    IsKInjective I' := sorry

end IsKInjective

namespace IsKInjective

/-- A K-injective DG module which is also injective after forgetting its differential. -/
class GradedInjective (I : Mod(𝒜, d)) : Prop extends IsKInjective I where
  /-- The underlying graded module is injective. -/
  [gradedInjective : (forgetToGraded 𝒜).IsInjectiveObj I]

namespace GradedInjective

/-- The combined condition exposes its two defining injectivity properties. -/
theorem iff (I : Mod(𝒜, d)) :
    GradedInjective I ↔
      IsKInjective I ∧ (forgetToGraded 𝒜).IsInjectiveObj I := sorry

/-- A morphism from an acyclic DG module to a graded-injective K-injective target extends
strictly across every monomorphism. -/
@[stacks 0FSW]
theorem exists_lift_of_acyclic {M M' I : Mod(𝒜, d)}
    (a : M ⟶ I) (b : M ⟶ M') [Mono b]
    (hM : Module.acyclic 𝒜 M)
    [GradedInjective I] :
    ∃ a' : M' ⟶ I, b ≫ a' = a := sorry

end GradedInjective

end IsKInjective

end


end SheafOfModules.RingedSite.DifferentialGradedModule.Module
