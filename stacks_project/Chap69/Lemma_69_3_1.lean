/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap69.Lemma_69_3_1_Quasicoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory

universe u

section

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.3.1: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. If `f` is quasi-compact and quasi-separated, then `R^i f_*` transforms quasi-coherent
`𝒪_X`-modules into quasi-coherent `𝒪_Y`-modules. -/
@[stacks 0720] #check
  (higherDirectImage.isQuasicoherent :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
      (F : X.Modules) [F.IsQuasicoherent] (i : ℕ),
      (higherDirectImage f F i).IsQuasicoherent)

#check QCoh.higherDirectImage

end

