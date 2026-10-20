module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Excellent.Locality

/-!
# Local criteria for (quasi-)excellent schemes

A scheme is quasi-excellent (resp. excellent) if and only if every affine-open
section ring is a quasi-excellent (resp. excellent) ring, equivalently if some
affine open cover has those section rings, and equivalently if some open cover
consists of quasi-excellent (resp. excellent) open subschemes. Every open
subscheme of a (quasi-)excellent scheme is (quasi-)excellent.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma [Stacks 0HAB] (1): a scheme is quasi-excellent if and only if the
section ring of every affine open is a quasi-excellent ring. -/
@[stacks 0HAB]
#check (AlgebraicGeometry.Scheme.quasiExcellent_iff_forall_affineOpen :
  ∀ X : Scheme.{u},
    X.QuasiExcellent ↔ ∀ U : X.affineOpens, IsQuasiExcellentRing.{u,u} Γ(X, U))

/- Lemma [Stacks 0HAB] (2): a scheme is quasi-excellent if and only if some
affine open cover has quasi-excellent section rings. -/
@[stacks 0HAB]
#check (AlgebraicGeometry.Scheme.quasiExcellent_iff_exists_affineOpenCover :
  ∀ X : Scheme.{u},
    X.QuasiExcellent ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsQuasiExcellentRing.{u,u} Γ(X, (𝒰.f i).opensRange))

/- Lemma [Stacks 0HAB] (3): a scheme is quasi-excellent if and only if some
open cover consists of quasi-excellent open subschemes. -/
@[stacks 0HAB]
#check (AlgebraicGeometry.Scheme.quasiExcellent_iff_exists_openCover :
  ∀ X : Scheme.{u},
    X.QuasiExcellent ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, Scheme.QuasiExcellent ((𝒰.f i).opensRange).toScheme)

/- Lemma [Stacks 0HAB] (4): every open subscheme of a quasi-excellent scheme is
quasi-excellent. -/
@[stacks 0HAB]
#check (AlgebraicGeometry.Scheme.quasiExcellent_toScheme :
  ∀ {X : Scheme.{u}} [X.QuasiExcellent] (U : X.Opens), Scheme.QuasiExcellent U.toScheme)

/- Lemma [Stacks 0HAB] (5): a scheme is excellent if and only if the section
ring of every affine open is an excellent ring. -/
@[stacks 0HAB]
#check (AlgebraicGeometry.Scheme.excellent_iff_forall_affineOpen :
  ∀ X : Scheme.{u},
    X.Excellent ↔ ∀ U : X.affineOpens, IsExcellentRing.{u,u} Γ(X, U))

/- Lemma [Stacks 0HAB] (6): a scheme is excellent if and only if some affine
open cover has excellent section rings. -/
@[stacks 0HAB]
#check (AlgebraicGeometry.Scheme.excellent_iff_exists_affineOpenCover :
  ∀ X : Scheme.{u},
    X.Excellent ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsExcellentRing.{u,u} Γ(X, (𝒰.f i).opensRange))

/- Lemma [Stacks 0HAB] (7): a scheme is excellent if and only if some open
cover consists of excellent open subschemes. -/
@[stacks 0HAB]
#check (AlgebraicGeometry.Scheme.excellent_iff_exists_openCover :
  ∀ X : Scheme.{u},
    X.Excellent ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, Scheme.Excellent ((𝒰.f i).opensRange).toScheme)

/- Lemma [Stacks 0HAB] (8): every open subscheme of an excellent scheme is
excellent. -/
@[stacks 0HAB]
#check (AlgebraicGeometry.Scheme.excellent_toScheme :
  ∀ {X : Scheme.{u}} [X.Excellent] (U : X.Opens), Scheme.Excellent U.toScheme)
