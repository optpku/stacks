module

public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap69.Lemma_69_20_2

/-!
# Coherence of higher direct images over a field

Higher direct images of coherent modules along a morphism of algebraic spaces
proper over a field remain coherent.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Higher direct images of coherent modules along a morphism between algebraic
spaces proper over a field are coherent. -/
instance higherDirectImage_isCoherent_of_proper_over_field
    {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
    [Proper (toBase X)] [Proper (toBase Y)]
    [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions Y.Modules] (𝒢 : Y.Modules) [𝒢.IsCoherent] (i : ℕ) :
    (higherDirectImage f 𝒢 i).IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
