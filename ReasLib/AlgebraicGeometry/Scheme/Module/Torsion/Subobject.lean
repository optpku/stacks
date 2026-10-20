/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Affine
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule

/-!
# Torsion subobjects of scheme modules

The torsion sections of a module on an integral scheme form a restriction-stable family of
submodules. This file constructs the associated subsheaf explicitly and records the
quasicoherence and torsion-freeness properties relevant to quasicoherent modules.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

namespace SectionTorsion

/-- The zero local section is torsion. -/
theorem Is.zero (ℱ : X.Modules) (U : X.Opens) :
    Is ℱ (0 : Γ(ℱ, U)) := sorry

/-- The sum of two torsion local sections is torsion. -/
theorem Is.add (ℱ : X.Modules) {U : X.Opens} {s t : Γ(ℱ, U)}
    (hs : Is ℱ s) (ht : Is ℱ t) :
    Is ℱ (s + t) := sorry

/-- Multiplying a torsion local section by a local function gives a torsion section. -/
theorem Is.smul (ℱ : X.Modules) {U : X.Opens} (r : Γ(X, U)) {s : Γ(ℱ, U)}
    (hs : Is ℱ s) :
    Is ℱ (r • s) := sorry

/-- Restriction of a torsion local section is torsion. -/
theorem Is.map (ℱ : X.Modules) {U V : (X.Opens)ᵒᵖ} (f : U ⟶ V)
    {s : ℱ.val.obj U} (hs : Is ℱ s) :
    Is ℱ (ℱ.presheaf.map f s) := sorry

/-- The restriction-stable presheaf submodule whose local sections are exactly the torsion
sections. -/
noncomputable def presheafSubmodule (ℱ : X.Modules) :
    PresheafOfModules.Submodule ℱ.val where
  obj U :=
    { carrier := fun s ↦ Is ℱ s
      zero_mem' := Is.zero ℱ U.unop
      add_mem' := fun hs ht ↦ hs.add ℱ ht
      smul_mem' := fun r _ hs ↦ hs.smul ℱ r }
  map f _ hs := Is.map ℱ f hs

/-- The presheaf of torsion local sections satisfies the sheaf condition. -/
theorem presheafSubmodule_isSheaf (ℱ : X.Modules) :
    TopCat.Presheaf.IsSheaf (presheafSubmodule ℱ).toPresheafOfModules.presheaf := sorry

end SectionTorsion

/-- The subobject whose sections on every open are exactly the torsion local sections. -/
noncomputable def torsionSubobject
    (ℱ : X.Modules) : Subobject ℱ :=
  let N := SectionTorsion.presheafSubmodule ℱ
  let T : X.Modules :=
    { val := N.toPresheafOfModules
      isSheaf := SectionTorsion.presheafSubmodule_isSheaf ℱ }
  let i : T ⟶ ℱ := { val := N.ι }
  @Subobject.mk _ _ _ _ i
    ((SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
      (inferInstance : Mono N.ι))

/-- A local section belongs to the torsion subobject exactly when all of its germs are torsion. -/
theorem mem_torsionSubobject_sections_iff
    (ℱ : X.Modules) (U : X.Opens) (s : Γ(ℱ, U)) :
    s ∈ SheafOfModules.Subobject.sections (torsionSubobject ℱ) (op U) ↔
      SectionTorsion.Is ℱ s := sorry

/-- On an affine open, the sections of the torsion subobject are the module-theoretic torsion
submodule. -/
theorem torsionSubobject_affineOpenSections_eq_torsion
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (U : X.affineOpens) :
    subobjectSectionsSubmoduleOnAffineOpen (torsionSubobject ℱ) U =
      Submodule.torsion (Γ(X, U)) (Γ(ℱ, U)) := sorry

/-- The torsion subobject of a quasicoherent module on an integral scheme is quasicoherent. -/
@[instance]
theorem torsionSubobject_isQuasicoherent
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((torsionSubobject ℱ : X.Modules)).IsQuasicoherent := sorry

/-- The quotient of a quasicoherent module by its torsion subobject is torsion free. -/
@[instance]
theorem cokernel_torsionSubobject_isTorsionFree
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsTorsionFree (cokernel (torsionSubobject ℱ).arrow) := sorry

/-- The torsion sections form a quasicoherent subobject whose quotient is torsion free. -/
theorem torsionSubobject_spec
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (∀ (U : X.Opens) (s : Γ(ℱ, U)),
        s ∈ SheafOfModules.Subobject.sections (torsionSubobject ℱ) (op U) ↔
          SectionTorsion.Is ℱ s) ∧
      ((torsionSubobject ℱ : X.Modules)).IsQuasicoherent ∧
      IsTorsionFree (cokernel (torsionSubobject ℱ).arrow) :=
  ⟨mem_torsionSubobject_sections_iff ℱ,
    torsionSubobject_isQuasicoherent ℱ,
    cokernel_torsionSubobject_isTorsionFree ℱ⟩

end AlgebraicGeometry.Scheme.Modules
