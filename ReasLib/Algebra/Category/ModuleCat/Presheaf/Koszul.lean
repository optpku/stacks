/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
public import ReasLib.RingTheory.Sequence.Koszul.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Koszul complexes of module presheaves

This file owns the topology-independent Koszul differential attached to a morphism from a
module presheaf to the structure module.  The differential is constructed sectionwise from the
ordinary Koszul differential and assembled into a morphism of module presheaves.  Sheaf-level
owners should sheafify this construction rather than rebuilding restriction-linear scalar data.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace PresheafOfModules.Koszul

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The underlying ring presheaf of the commutative ring presheaf `O`. -/
abbrev RingPresheaf := CategoryTheory.Presheaf.ringPresheafOfComm O

/-- The degree-`n + 1` Koszul differential over one object of the site. -/
noncomputable abbrev differentialApp
    {F : PresheafOfModules.{w} (RingPresheaf O)}
    (phi : F ⟶ PresheafOfModules.unit (RingPresheaf O))
    (n : ℕ) (U : Cᵒᵖ) :
    ExteriorPower.obj O F (n + 1) U ⟶ ExteriorPower.obj O F n U :=
  _root_.koszulDifferential (R := O.obj U) (E := F.obj U) (phi.app U).hom n

/-- Sectionwise Koszul differentials commute with restriction of module-presheaf sections. -/
theorem differentialApp_naturality
    {F : PresheafOfModules.{w} (RingPresheaf O)}
    (phi : F ⟶ PresheafOfModules.unit (RingPresheaf O)) (n : ℕ)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    ExteriorPower.map O F (n + 1) i ≫
        (ModuleCat.restrictScalars (O.map i).hom).map (differentialApp O phi n V) =
      differentialApp O phi n U ≫ ExteriorPower.map O F n i := sorry

/-- The degree-`n + 1` Koszul differential as a morphism of module presheaves. -/
@[stacks 062K "presheaf differential"]
noncomputable def differential
    {F : PresheafOfModules.{w} (RingPresheaf O)}
    (phi : F ⟶ PresheafOfModules.unit (RingPresheaf O)) (n : ℕ) :
    ExteriorPower.presheaf O F (n + 1) ⟶ ExteriorPower.presheaf O F n where
  app := differentialApp O phi n
  naturality := differentialApp_naturality O phi n

/-- Consecutive Koszul differentials of module presheaves compose to zero. -/
theorem differential_sq
    {F : PresheafOfModules.{w} (RingPresheaf O)}
    (phi : F ⟶ PresheafOfModules.unit (RingPresheaf O)) (n : ℕ) :
    differential O phi (n + 1) ≫ differential O phi n = 0 := sorry

/-- The Koszul chain complex of a morphism from a module presheaf to the structure module. -/
@[stacks 062K "module-presheaf chain complex"]
noncomputable def complex
    {F : PresheafOfModules.{w} (RingPresheaf O)}
    (phi : F ⟶ PresheafOfModules.unit (RingPresheaf O)) :
    ChainComplex (PresheafOfModules.{w} (RingPresheaf O)) ℕ :=
  ChainComplex.of (fun n ↦ ExteriorPower.presheaf O F n)
    (differential O phi) (differential_sq O phi)

/-- The degree-`n` term of a module-presheaf Koszul complex is its degree-`n` exterior power. -/
theorem complex_X
    {F : PresheafOfModules.{w} (RingPresheaf O)}
    (phi : F ⟶ PresheafOfModules.unit (RingPresheaf O)) (n : ℕ) :
    (complex O phi).X n = ExteriorPower.presheaf O F n := sorry

/-- The differential from degree `n + 1` to degree `n` in a module-presheaf Koszul complex is
the canonical sectionwise Koszul differential. -/
theorem complex_d
    {F : PresheafOfModules.{w} (RingPresheaf O)}
    (phi : F ⟶ PresheafOfModules.unit (RingPresheaf O)) (n : ℕ) :
    (complex O phi).d (n + 1) n = differential O phi n := sorry

end PresheafOfModules.Koszul

