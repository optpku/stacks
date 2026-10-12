/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRingSheafificationMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness and sheafification of module presheaves

This file owns the two reusable ways of proving that the sheafification of a module presheaf is
flat: categorical flatness before sheafification, and coverwise flatness of sections.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [Functor.Monoidal (moduleSheafification J 𝒪)]

/-- Sheafification carries a flat module presheaf to a flat module sheaf. -/
@[stacks 03ET, instance]
theorem sheafification_isFlat
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) [IsFlat ℱ] :
    SheafOfModules.RingedSite.IsFlat
      (commRingSheafification J 𝒪) ((moduleSheafification J 𝒪).obj ℱ) := sorry

/-- Coverwise flatness of sections implies flatness after sheafification. -/
@[stacks 0GN1]
theorem sheafification_isFlat_of_locally_flat
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hlocal :
      ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
          Module.Flat (𝒪.obj (op V)) (ℱ.obj (op V))) :
    SheafOfModules.RingedSite.IsFlat
      (commRingSheafification J 𝒪) ((moduleSheafification J 𝒪).obj ℱ) := sorry

end PresheafOfModules
