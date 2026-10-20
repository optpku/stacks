/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import ReasLib.Algebra.Module.IdealPower.Submodule
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ext and Tor maps for adic stages

This leaf contains the small derived-category maps induced by the canonical inclusion from
`Ideal.PowerSubmodule.stage I M n` to `M`.  It is separate from the filtered-homology owner so
that Ext/Tor consumers can reuse the maps without importing a chapter file.
@stack 0G3K
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

noncomputable section

universe u v

namespace CategoryTheory.DerivedCategory.IdealPower

variable {A : Type u} [CommRing A]

/-- The Tor map induced by the inclusion of an adic stage in the first variable.

The shared universe is forced by Mathlib's current monoidal structure on `ModuleCat`, whose
module universe must equal the universe of the ring. -/
@[stacks 0G3K "Tor map induced by an adic stage inclusion"]
noncomputable abbrev subtypeTorMap
    (I : Ideal A) (M N : ModuleCat.{u} A) (n p : ℕ)
    [HasProjectiveResolutions (ModuleCat.{u} A)] :
    ((Tor (ModuleCat.{u} A) p).flip.obj N).obj (Ideal.PowerSubmodule.stageObj I M n) ⟶
      ((Tor (ModuleCat.{u} A) p).flip.obj N).obj M :=
  (((Tor (ModuleCat.{u} A) p).flip.obj N).map
    (ModuleCat.ofHom (Ideal.PowerSubmodule.subtype I M n)))

/-- The Ext restriction map induced by the inclusion of an adic stage in the first variable. -/
@[stacks 0G3K "Ext precomposition along an adic stage inclusion"]
noncomputable abbrev subtypeExtPrecomp
    (I : Ideal A) (M N : ModuleCat.{v} A) (n p : ℕ)
    [HasExt (ModuleCat.{v} A)] :
    Ext M N p →ₗ[A]
      Ext (Ideal.PowerSubmodule.stageObj I M n) N p :=
  (mk₀ (ModuleCat.ofHom (Ideal.PowerSubmodule.subtype I M n))).precompOfLinear A N
    (zero_add p)

/-- The Ext map induced by the inclusion of an adic stage in the second variable. -/
@[stacks 0G3K "Ext postcomposition along an adic stage inclusion"]
noncomputable abbrev subtypeExtPostcomp
    (I : Ideal A) (M N : ModuleCat.{v} A) (n p : ℕ)
    [HasExt (ModuleCat.{v} A)] :
    Ext M (Ideal.PowerSubmodule.stageObj I N n) p →ₗ[A] Ext M N p :=
  (mk₀ (ModuleCat.ofHom (Ideal.PowerSubmodule.subtype I N n))).postcompOfLinear A M
    (add_zero p)

end CategoryTheory.DerivedCategory.IdealPower
