/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Locality
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 28.13.5

The universally Japanese specializations of affine-locality are owned by
`ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Locality`.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.13.5

For a scheme `X`, universal Japanese-ness is equivalent to the corresponding
condition on every affine open section ring.
-/
@[stacks 033W] #check
  (AlgebraicGeometry.Scheme.UniversallyJapanese.iff_forall_affineOpen :
    ∀ X : Scheme.{u},
      X.UniversallyJapanese ↔
        ∀ U : X.affineOpens, UniversallyJapaneseRing.{u, u} (Γ(X, U)))

#check (AlgebraicGeometry.Scheme.UniversallyJapanese.iff_exists_affineOpenCover :
  ∀ X : Scheme.{u},
    X.UniversallyJapanese ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, UniversallyJapaneseRing.{u, u} (Γ(X, (𝒰.f i).opensRange)))

#check (AlgebraicGeometry.Scheme.universallyJapanese_iff_exists_openCover_by_universallyJapanese :
  ∀ X : Scheme.{u},
    X.UniversallyJapanese ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀, AlgebraicGeometry.Scheme.UniversallyJapanese ((𝒰.f i).opensRange).toScheme)

#check (AlgebraicGeometry.Scheme.universallyJapanese_toScheme :
  ∀ (X : Scheme.{u}) (_ : X.UniversallyJapanese) (U : X.Opens),
    AlgebraicGeometry.Scheme.UniversallyJapanese U.toScheme)
