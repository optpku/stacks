/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 37.16.5 (1): if `ℱ` is finitely presented and flat over `S`, then its
relative-flatness locus over `Y` is open in `X`. -/
@[stacks 05VJ]
#check (AlgebraicGeometry.Scheme.Modules.isOpen_flatOverAt_of_flatOver :
  ∀ {S : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFiniteType Y.hom]
    (ℱ : X.left.Modules) [ℱ.IsFinitePresentation]
    (h_flat : flatOver ℱ X.hom),
    IsOpen {x : X.left | flatOverAt ℱ f.left x})

/- Lemma 37.16.5 (2): the relative-flatness locus of `ℱ` commutes with every
base change `s : S' ⟶ S`. -/
@[stacks 05VJ]
#check (AlgebraicGeometry.Scheme.Modules.flatOverAt_baseChange_eq_preimage :
  ∀ {S S' : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFiniteType Y.hom]
    (ℱ : X.left.Modules) [ℱ.IsFinitePresentation]
    (h_flat : flatOver ℱ X.hom) (s : S' ⟶ S),
    {x' : ((Over.pullback s).obj X).left |
        flatOverAt (Scheme.Modules.baseChangeModule X.hom s ℱ)
          ((Over.pullback s).map f).left x'} =
      (pullback.fst X.hom s).base ⁻¹' {x : X.left | flatOverAt ℱ f.left x})

end AlgebraicGeometry.Scheme.Modules
