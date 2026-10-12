/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Relative flatness of modules over inverse limits

Relative flatness of finitely presented quasi-coherent modules descends along directed inverse
limits of quasi-compact, quasi-separated schemes with affine transition morphisms.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Limit

/-- If a finitely presented quasi-coherent module over a morphism of finitely presented schemes
becomes flat after base change to a directed inverse limit, then it is already flat after base
change to some stage. -/
theorem exists_flatOver_stage_of_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) (Xi Yi : Over (D.obj i))
    [Scheme.Hom.FinitePresentation Xi.hom]
    [Scheme.Hom.FinitePresentation Yi.hom]
    (φi : Xi ⟶ Yi)
    (ℱi : Xi.left.Modules) [ℱi.IsQuasicoherent] [ℱi.IsFinitePresentation]
    (hflat : Scheme.Modules.flatOver
      (Scheme.Modules.baseChangeModule Xi.hom (c.π.app i) ℱi)
      ((Over.pullback (c.π.app i)).map φi).left) :
    ∃ (i' : I) (hii' : i ≤ i'),
      Scheme.Modules.flatOver
        (Scheme.Modules.baseChangeModule Xi.hom (D.map (homOfLE hii')) ℱi)
        ((Over.pullback (D.map (homOfLE hii'))).map φi).left := sorry

end AlgebraicGeometry.Scheme.Modules.Limit
