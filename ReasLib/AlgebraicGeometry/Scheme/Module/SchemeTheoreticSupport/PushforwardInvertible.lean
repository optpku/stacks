/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite-type quasicoherent module with scheme-theoretic support finite over the target
of a finite-type separated morphism and invertible pushforward is the pushforward of that
invertible module along a section of the morphism. -/
theorem exists_section_pushforward_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [f.FiniteType] [IsSeparated f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (h_support : IsFinite ((Scheme.Modules.schemeTheoreticSupport F).subschemeι ≫ f))
    [Scheme.Modules.Invertible ((Scheme.Modules.pushforward f).obj F)] :
    ∃ s : Y ⟶ X, s ≫ f = 𝟙 Y ∧
      Nonempty (F ≅ (Scheme.Modules.pushforward s).obj
        ((Scheme.Modules.pushforward f).obj F)) := sorry

/-- A finite-type quasicoherent module supported on the image of a section of a finite-type
separated morphism, whose pushforward is invertible over a reduced target, is the pushforward of
that module along the section. -/
theorem section_pushforward_iso_of_support_subset
    {X Y : Scheme.{u}} (f : X ⟶ Y) [f.FiniteType] [IsSeparated f]
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent]
    (h_support : Scheme.Modules.moduleSupport F ⊆ Set.range s.base)
    [Scheme.Modules.Invertible ((Scheme.Modules.pushforward f).obj F)] [IsReduced Y] :
    Nonempty (F ≅ (Scheme.Modules.pushforward s).obj
      ((Scheme.Modules.pushforward f).obj F)) := sorry

end AlgebraicGeometry.Scheme.Modules
