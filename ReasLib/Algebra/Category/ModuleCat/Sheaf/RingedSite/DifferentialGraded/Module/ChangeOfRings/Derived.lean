/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.QuasiIso
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat.Resolution
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived change of rings for differential graded module sheaves

Extension of scalars is derived through the canonical localization of DG modules at
quasi-isomorphisms.  Restriction preserves quasi-isomorphisms and therefore descends directly.
The underived extension-restriction adjunction then induces a canonical adjunction between these
two functors on derived categories.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MorphismProperty
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.ChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {A B : DGA(𝒪)}

/-- Ordinary extension of scalars followed by the target derived localization. -/
abbrev extensionSource (f : A ⟶ B) :
    Mod(A, d) ⥤ DerivedCategory B :=
  ChangeOfRings.extension f ⋙ DerivedCategory.Q B

/-- The source-level assertion that extension of scalars admits a total left derived functor. -/
abbrev HasExtension (f : A ⟶ B) : Prop :=
  Functor.LeftDerived.EverywhereDefined (extensionSource f) (Module.quasiIso A)

/-- Fixed-base-good resolutions define derived extension of scalars at every DG module. -/
instance hasExtension (f : A ⟶ B) : HasExtension f := sorry

/-- Restriction of scalars followed by the source derived localization. -/
abbrev restrictionSource (f : A ⟶ B) :
    Mod(B, d) ⥤ DerivedCategory A :=
  ChangeOfRings.restriction f ⋙ DerivedCategory.Q A

/-- Restriction of scalars preserves quasi-isomorphisms. -/
@[stacks 0BYX "restriction of DG module sheaves preserves quasi-isomorphisms"]
theorem restriction_inverts (f : A ⟶ B) :
    (Module.quasiIso B).IsInvertedBy (restrictionSource f) := sorry

/-- The source-level assertion that restriction of scalars admits a total right derived functor. -/
abbrev HasRestriction (f : A ⟶ B) : Prop :=
  Functor.RightDerived.EverywhereDefined (restrictionSource f) (Module.quasiIso B)

/-- Restriction of scalars has an everywhere-defined total right derived functor. -/
instance hasRestriction (f : A ⟶ B) : HasRestriction f := sorry

/-- Extension and restriction form an absolute total-derived pair for the canonical DG-module
localizations. -/
instance hasDerivedPair (f : A ⟶ B) :
    Adjunction.TotalDerived.HasPair
      (G := ChangeOfRings.extension f) (F := ChangeOfRings.restriction f)
      (Module.quasiIso A) (Module.quasiIso B)
      (L1 := DerivedCategory.Q A) (L2 := DerivedCategory.Q B) := sorry

namespace Derived

/-- Canonical derived extension of scalars for differential graded module sheaves. -/
@[stacks 0BYX "derived extension of scalars for DG module sheaves"]
noncomputable def extension (f : A ⟶ B) : DerivedCategory A ⥤ DerivedCategory B :=
  (extensionSource f).totalLeftDerived (DerivedCategory.Q A) (Module.quasiIso A)

/-- The canonical comparison from derived extension to ordinary extension followed by
localization. -/
noncomputable def extensionCounit (f : A ⟶ B) :
    DerivedCategory.Q A ⋙ extension f ⟶ extensionSource f :=
  (extensionSource f).totalLeftDerivedCounit (DerivedCategory.Q A) (Module.quasiIso A)

/-- The canonical extension functor and its counit form a left-derived functor model. -/
instance extension_isLeftDerived (f : A ⟶ B) :
    (extension f).IsLeftDerivedFunctor (extensionCounit f) (Module.quasiIso A) := sorry

/-- Canonical derived restriction of scalars for differential graded module sheaves. -/
@[stacks 0BYX "derived restriction of scalars for DG module sheaves"]
noncomputable def restriction (f : A ⟶ B) : DerivedCategory B ⥤ DerivedCategory A :=
  Localization.lift (restrictionSource f) (restriction_inverts f) (DerivedCategory.Q B)

/-- Derived restriction factors ordinary restriction through the canonical localizations. -/
noncomputable def restrictionFac (f : A ⟶ B) :
    DerivedCategory.Q B ⋙ restriction f ≅ restrictionSource f :=
  Localization.fac (restrictionSource f) (restriction_inverts f) (DerivedCategory.Q B)

/-- Derived extension of scalars is left adjoint to derived restriction of scalars. -/
@[stacks 0BYX "derived extension-restriction adjunction for DG module sheaves"]
noncomputable def adjunction (f : A ⟶ B) : extension f ⊣ restriction f :=
  Adjunction.TotalDerived.withDescendedRight
    (ChangeOfRings.adjunction f) (Module.quasiIso A) (Module.quasiIso B)
    (restriction_inverts f) (Iso.refl _)

/-- The reusable Hom equivalence for derived extension and restriction of scalars. -/
@[stacks 0BYX "derived extension-restriction Hom equivalence for DG module sheaves"]
noncomputable def homEquiv (f : A ⟶ B)
    (M : DerivedCategory A) (N : DerivedCategory B) :
    ((extension f).obj M ⟶ N) ≃ (M ⟶ (restriction f).obj N) :=
  (adjunction f).homEquiv M N

/-- Lemma 24.30.1 (0FTZ): derived extension of scalars along a quasi-isomorphism of
differential graded algebra sheaves is an equivalence. -/
@[stacks 0FTZ "derived extension along a quasi-isomorphism of DGA sheaves"]
theorem extension_isEquivalence (f : A ⟶ B)
    (hf : DifferentialGradedAlgebra.quasiIso f) :
    Functor.IsEquivalence (extension f) := sorry

/-- Derived restriction of scalars along a quasi-isomorphism of differential graded algebra
sheaves is an equivalence. -/
theorem restriction_isEquivalence (f : A ⟶ B)
    (hf : DifferentialGradedAlgebra.quasiIso f) :
    Functor.IsEquivalence (restriction f) := sorry

end Derived

end SheafOfModules.RingedSite.DifferentialGradedModule.ChangeOfRings

end
