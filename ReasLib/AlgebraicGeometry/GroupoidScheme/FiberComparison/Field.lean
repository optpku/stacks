/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.FiberComparison

/-!
# Source base change for groupoid schemes over fields

This module compares points of the arrow scheme after extending the field over which the
object scheme is defined.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- After a common field extension, two arrows of a groupoid scheme over a field spectrum lift
to points related by an automorphism over the extended field. -/
theorem existsSourceBaseChangeIso_mapPoints
    {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) (r r' : G.R.left) :
    ∃ (K : Type u) (_ : Field K) (ι : k →+* K),
      let f := Spec.map (CommRingCat.ofHom ι) ≫ eU.hom
      let R' : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd G.s.left f)
      ∃ (φ : R' ≅ R') (r₁ r₂ : R'.left),
        φ.hom.left r₁ = r₂ ∧
          pullback.fst G.s.left f r₁ = r ∧
          pullback.fst G.s.left f r₂ = r' := sorry

end AlgebraicGeometry.GroupoidScheme
