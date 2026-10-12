/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Limit.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 32.10.4: relative flatness of a finitely presented quasi-coherent module after base
change to a directed inverse limit descends to some stage. -/
@[stacks 05LY] #check
  (AlgebraicGeometry.Scheme.Modules.Limit.exists_flatOver_stage_of_limit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
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
        ((Over.pullback (c.π.app i)).map φi).left),
      ∃ (i' : I) (hii' : i ≤ i'),
        Scheme.Modules.flatOver
          (Scheme.Modules.baseChangeModule Xi.hom (D.map (homOfLE hii')) ℱi)
          ((Over.pullback (D.map (homOfLE hii'))).map φi).left)
