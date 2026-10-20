module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Locality
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 28.13.6

The Nagata specializations of affine-locality are owned by
`ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Locality`.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.13.6: a scheme is Nagata exactly when all affine-open section rings
are Nagata, equivalently when it has an affine cover by such rings or an open
cover by Nagata schemes; every open subscheme of a Nagata scheme is Nagata. -/
@[stacks 033X] #check
  (AlgebraicGeometry.Scheme.nagata_iff_forall_affineOpen_sectionsRing_nagataRing :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.Scheme.Nagata X ↔
        ∀ U : X.affineOpens, NagataRing (Γ(X, U)))

#check
  (AlgebraicGeometry.Scheme.nagata_iff_exists_affineOpenCover_sectionsRing_nagataRing :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.Scheme.Nagata X ↔
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀, NagataRing (Γ(X, (𝒰.f i).opensRange)))

#check
  (AlgebraicGeometry.Scheme.nagata_iff_exists_openCover_by_nagata :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.Scheme.Nagata X ↔
        ∃ 𝒰 : X.OpenCover,
          ∀ i : 𝒰.I₀,
            AlgebraicGeometry.Scheme.Nagata ((𝒰.f i).opensRange).toScheme)

#check
  (AlgebraicGeometry.Scheme.nagata_toScheme :
    ∀ {X : AlgebraicGeometry.Scheme.{u}},
      AlgebraicGeometry.Scheme.Nagata X →
        ∀ U : X.Opens, AlgebraicGeometry.Scheme.Nagata U.toScheme)
