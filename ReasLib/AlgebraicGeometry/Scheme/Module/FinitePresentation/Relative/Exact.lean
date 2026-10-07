module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Module.FinitePresentation.Relative.Exact
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative

/-!
# Relative finite presentation in short exact sequences

Relative finite presentation for quasicoherent scheme modules is closed under extensions and
under quotients by finite-type submodules.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsFinitePresentationOver

/-- In a short exact sequence of quasicoherent modules over a scheme, relative finite
presentation of the outer terms implies relative finite presentation of the middle term. -/
theorem middle_of_shortExact {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {C : ShortComplex X.Modules} [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent]
    [C.X₃.IsQuasicoherent] (hC : C.ShortExact) (h₁ : C.X₁.IsFinitePresentationOver f)
    (h₃ : C.X₃.IsFinitePresentationOver f) : C.X₂.IsFinitePresentationOver f := sorry

/-- In a short exact sequence of quasicoherent modules over a scheme, a finite-type left term
and a relatively finitely presented middle term imply relative finite presentation of the right
term. -/
theorem right_of_shortExact {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {C : ShortComplex X.Modules} [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent]
    [C.X₃.IsQuasicoherent] [C.X₁.IsFiniteType] (hC : C.ShortExact)
    (h₂ : C.X₂.IsFinitePresentationOver f) : C.X₃.IsFinitePresentationOver f := sorry

end AlgebraicGeometry.Scheme.Modules.IsFinitePresentationOver
