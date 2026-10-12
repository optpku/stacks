/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.OpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.22.9: let `X` be a quasi-compact and quasi-separated scheme, let `F` be a
finite-type quasi-coherent `O_X`-module, and let `j : U ⟶ X` be a quasi-compact open immersion
such that `F.restrict j` is of finite presentation. Then there is a finitely presented module
`G` and an epimorphism `φ : G ⟶ F` whose restriction along `j` is an isomorphism. -/
@[stacks 080V] #check
  (AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_epi_restrictIso :
    ∀ {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      [(F.restrict j).IsFinitePresentation],
      ∃ (G : X.Modules) (_ : G.IsFinitePresentation) (φ : G ⟶ F),
        Epi φ ∧ IsIso ((AlgebraicGeometry.Scheme.Modules.restrictFunctor j).map φ))
