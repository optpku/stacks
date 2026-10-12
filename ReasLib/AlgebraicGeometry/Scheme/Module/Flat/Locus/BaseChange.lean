/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.FiberCriterion.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus

/-!
# Base change of relative flatness loci

This module records compatibility of open relative-flatness loci with flat base change and
arbitrary base change when the module is flat over the base.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The open relative-flatness locus of a finitely presented module is carried to its inverse
image around a cartesian square whose base morphism is flat. -/
@[stacks 047C]
theorem flatOverAt_open_eq_preimage_of_isPullback_of_flat_base
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hcart : IsPullback g' f' f g)
    [Flat g] [LocallyOfFinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (W : X.Opens) (W' : X'.Opens)
    (hW : (W : Set X) = {x : X | flatOverAt ℱ f x})
    (hW' : (W' : Set X') =
      {x' : X' | flatOverAt ((Scheme.Modules.pullback g').obj ℱ) f' x'}) :
    W' = g' ⁻¹ᵁ W := sorry

/-- Let `X` and `Y` be `S`-schemes, with `X` locally of finite presentation and `Y` locally
of finite type over `S`. If a finitely presented module on `X` is flat over `S`, then its
relative-flatness locus for an `S`-morphism from `X` to `Y` is open. -/
theorem isOpen_flatOverAt_of_flatOver {S : Scheme.{u}}
    (X Y : Over S) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFiniteType Y.hom]
    (ℱ : X.left.Modules) [ℱ.IsFinitePresentation]
    (h_flat : flatOver ℱ X.hom) :
    IsOpen {x : X.left | flatOverAt ℱ f.left x} := sorry

/-- Let `X` and `Y` be `S`-schemes, with `X` locally of finite presentation and `Y` locally
of finite type over `S`. If a finitely presented module on `X` is flat over `S`, then its
relative-flatness locus pulls back along every morphism `S' ⟶ S`. -/
theorem flatOverAt_baseChange_eq_preimage {S S' : Scheme.{u}}
    (X Y : Over S) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFiniteType Y.hom]
    (ℱ : X.left.Modules) [ℱ.IsFinitePresentation]
    (h_flat : flatOver ℱ X.hom) (s : S' ⟶ S) :
    {x' : ((Over.pullback s).obj X).left |
        flatOverAt (Scheme.Modules.baseChangeModule X.hom s ℱ)
          ((Over.pullback s).map f).left x'} =
      (pullback.fst X.hom s).base ⁻¹' {x : X.left | flatOverAt ℱ f.left x} := sorry

end AlgebraicGeometry.Scheme.Modules
