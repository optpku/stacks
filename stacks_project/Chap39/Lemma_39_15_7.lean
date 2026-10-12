/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.CardinalGeneration
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 39.15.7: if the source and target of a groupoid scheme are flat, one cardinal
uniformly bounds a directed, exhaustive family of generated equivariant quasi-coherent
submodules of every equivariant quasi-coherent module. -/
@[stacks 077U] #check
  (AlgebraicGeometry.GroupoidScheme.QCoh.exists_cardinal_kappaGeneratedSubobjects_isDirectedColimit :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S) [Flat G.s.left] [Flat G.t.left],
      ∃ κ : Cardinal.{u}, ∀ A : G.QCoh,
        DirectedOn (· ≤ ·) (GroupoidScheme.QCoh.kappaGeneratedSubobjects G κ A) ∧
          IsLUB (GroupoidScheme.QCoh.kappaGeneratedSubobjects G κ A)
            (⊤ : Subobject A.obj))
