module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_11_2_Flat_base_change_BaseChange

/-!
# Lemma 69.20.3

Cohomology of a coherent module on an algebraic space proper over a Noetherian
affine base is a finite module.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Lemma 69.20.3: if `A` is a Noetherian ring, `f : X ⟶ ofOver (Over.mk σA)` is a proper
morphism of algebraic spaces to `Spec(A)` over a scheme `S`, and `F` is a coherent `𝒪_X`-module,
then `cohomologyOver σA f F i` is a finite `A`-module for every `i : ℕ`. Here
`ofOver (Over.mk σA)` is `Spec(A)` as an algebraic space over `S`, and `cohomologyOver` is the
`A`-module `H^i(X, F)`. -/
@[stacks 08AS]
instance cohomologyOver_isFinite
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA)) [Proper f]
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    Module.Finite A (cohomologyOver σA f F i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
