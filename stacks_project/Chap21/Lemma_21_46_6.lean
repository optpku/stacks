/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.46.6

The distinguished-triangle propagation laws for Tor-amplitude are owned in abstract monoidal
form by `DerivedTensor.TorAmplitude`; the ringed-site statement is their canonical module-sheaf
specialization.
-/

/- Lemma 21.46.6 (1) (08G2): if the first vertex has Tor-amplitude in
`[a + 1, b + 1]` and the second in `[a, b]`, then the third has Tor-amplitude in `[a, b]`. -/
@[stacks 08G2 "(1)"]
#check @CategoryTheory.DerivedCategory.DerivedTensor.TorAmplitude.obj₃_of_distinguished

/- Lemma 21.46.6 (2) (08G2): if the outer vertices have Tor-amplitude in `[a, b]`, then the
middle vertex has Tor-amplitude in `[a, b]`. -/
@[stacks 08G2 "(2)"]
#check @CategoryTheory.DerivedCategory.DerivedTensor.TorAmplitude.obj₂_of_distinguished

/- Lemma 21.46.6 (3) (08G2): if the second vertex has Tor-amplitude in
`[a + 1, b + 1]` and the third in `[a, b]`, then the first has Tor-amplitude in
`[a + 1, b + 1]`. -/
@[stacks 08G2 "(3)"]
#check @CategoryTheory.DerivedCategory.DerivedTensor.TorAmplitude.obj₁_of_distinguished

#check @CategoryTheory.DerivedCategory.DerivedTensor.torAmplitudeIn_isTriangulatedClosed₂
#check @CategoryTheory.DerivedCategory.DerivedTensor.finiteTorDimension_isTriangulated

end
