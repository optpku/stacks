/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.DualNumberPullback

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-! Lemma 90.10.7: dual-number pullback compatibility checks. -/
#check (dualNumberPullback : ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k] (A : ArtinianLocalAlgCat Λ k),
  ArtinianLocalAlgCat Λ k)

#check (dualNumberPullbackFst : ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k] (A : ArtinianLocalAlgCat Λ k),
  dualNumberPullback A ⟶ A)

#check (dualNumberPullbackSnd : ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k] (A : ArtinianLocalAlgCat Λ k),
  dualNumberPullback A ⟶ dualNumber Λ k)

#check (dualNumberPullbackSection : ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k] (A : ArtinianLocalAlgCat Λ k),
  A ⟶ dualNumberPullback A)

#check (isPullback_dualNumberPullback : ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k] (A : ArtinianLocalAlgCat Λ k),
  IsPullback (dualNumberPullbackFst A) (dualNumberPullbackSnd A)
    (toResidue A) (dualNumberToResidue Λ k))

end ArtinianLocalAlgCat
