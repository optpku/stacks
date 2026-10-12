/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a separated finite-type morphism and a finite-type quasicoherent module whose
support on every fibre is finite, relative purity, finiteness of the scheme-theoretic
support over the base, and universal relative purity are equivalent. -/
theorem isPureOver_tfae_isFinite_schemeTheoreticSupport_isUniversallyPureOver
    {X S : Scheme.{u}} (f : X ⟶ S) [f.FiniteType] [IsSeparated f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (hfinite : ∀ s : S,
      (Scheme.Modules.moduleSupport
        ((Scheme.Modules.pullback (f.fiberι s)).obj F)).Finite) :
    List.TFAE [
      F.IsPureOver f,
      IsFinite ((schemeTheoreticSupport F).subschemeι ≫ f),
      F.IsUniversallyPureOver f] := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- Under a quasi-finite separated morphism, the source scheme is pure relative to the
base exactly when the morphism is finite. -/
theorem isPureOver_iff_isFinite_of_quasiFinite_of_isSeparated
    {X S : Scheme.{u}} (f : X ⟶ S) [Hom.QuasiFinite f] [IsSeparated f] :
    IsPureOver f ↔ IsFinite f := sorry

end AlgebraicGeometry.Scheme
