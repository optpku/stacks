/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Subobject.Lattice
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent

/-!
# Quasi-coherent ideal sheaves on algebraic spaces

An ideal sheaf on an algebraic space is a subobject of `𝒪_X` on the small étale
site. Quasi-coherence is recorded as an ambient property of that subobject, so
sums and intersections of quasi-coherent ideals remain quasi-coherent.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An ideal subobject of an algebraic space is a subobject of `𝒪_X`, viewed as a
module over itself on the small étale site. -/
abbrev IdealSubobject {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  Subobject (SheafOfModules.unit (structureSheaf X) : X.Modules)

/-- The module sheaf represented by an ideal subobject. -/
noncomputable abbrev IdealSubobject.toModule {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) : X.Modules :=
  Subobject.underlying.obj I

/-- The module represented by an ideal subobject is the chosen underlying object of
the subobject. -/
theorem IdealSubobject.toModule_def {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) :
    I.toModule = Subobject.underlying.obj I :=
  rfl

/-- `toModule` recovers the coercion of an ideal subobject to an `𝒪_X`-module. -/
theorem IdealSubobject.toModule_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) :
    I.toModule = (I : X.Modules) :=
  rfl

/-- A quasi-coherent ideal sheaf on an algebraic space is a quasi-coherent
`𝒪_X`-submodule of `𝒪_X`.

This class is a thin specialization of `SheafOfModules.IsQuasicoherent` along
`IdealSubobject.toModule`. Its historical spelling is retained for compatibility;
`IsQuasiCoherent.quasiCoherent` and `IsQuasiCoherent.of_isQuasicoherent` provide
the two instance bridges, and `IsQuasiCoherent.spec` states their equivalence. -/
@[mk_iff]
class IsQuasiCoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) : Prop where
  /-- The underlying module sheaf of `I` is quasi-coherent. -/
  quasiCoherent : quasiCoherentModuleProperty X I.toModule

namespace IsQuasiCoherent

attribute [instance] quasiCoherent

/-- Quasi-coherence of the underlying module gives quasi-coherence of the ideal.
Together with the field instance `quasiCoherent`, this identifies the ideal
specialization with mathlib's module predicate. -/
instance (priority := low) of_isQuasicoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [I.toModule.IsQuasicoherent] : IsQuasiCoherent I :=
  ⟨inferInstance⟩

/-- The zero ideal sheaf on an algebraic space is quasi-coherent. -/
instance bot {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsQuasiCoherent (⊥ : IdealSubobject X) :=
  sorry

/-- The unit ideal sheaf on an algebraic space is quasi-coherent. -/
instance top {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsQuasiCoherent (⊤ : IdealSubobject X) :=
  sorry

/-- The intersection of quasi-coherent ideal sheaves is quasi-coherent. -/
instance inf {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    IsQuasiCoherent (I ⊓ J) :=
  sorry

/-- The sum of quasi-coherent ideal sheaves is quasi-coherent. -/
instance sup {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    IsQuasiCoherent (I ⊔ J) :=
  sorry

/-- Quasi-coherence of an ideal sheaf is quasi-coherence of its underlying
`𝒪_X`-module. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X) :
    IsQuasiCoherent I ↔ quasiCoherentModuleProperty X I.toModule :=
  isQuasiCoherent_iff I

end IsQuasiCoherent

end AlgebraicGeometry.AlgebraicSpace
