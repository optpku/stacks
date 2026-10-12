/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.ChernClass
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X' X S' S : Scheme.{u}}
variable {f : X' ⟶ X} {h' : X' ⟶ S'} {h : X ⟶ S} {g : S' ⟶ S}

namespace ChernClassContext

/-- Pullback maps between the logarithmic, de Rham, and Hodge realizations attached to a
commutative square, together with their lower-level comparison laws. -/
structure Pullback (sq : CommSq f h' h g)
    (C : ChernClassContext h) (C' : ChernClassContext h') where
  /-- Pullback on the cohomology of the truncated relative de Rham complex. -/
  dlogPullback : hodgeSource h 1 2 →+ hodgeSource h' 1 2
  /-- Pullback on degree-two relative de Rham cohomology. -/
  deRhamPullback : cohomology h 2 →+ cohomology h' 2
  /-- Pullback on `H¹(Ω¹)` Hodge cohomology. -/
  hodgePullback : hodgeCohomology h 1 1 →+ hodgeCohomology h' 1 1
  /-- The logarithmic cohomology map commutes with Picard pullback. -/
  dlogNaturality : ∀ x : X.PicardGroup,
    dlogPullback (C.dlogCohomologyMap x) =
      C'.dlogCohomologyMap (Scheme.Hom.picardPullback f x)
  /-- Pullback commutes with the map from truncated to relative de Rham cohomology. -/
  deRhamComparison : ∀ z : hodgeSource h 1 2,
    deRhamPullback ((hodgeMap h 1 2).hom z) =
      (hodgeMap h' 1 2).hom (dlogPullback z)
  /-- Pullback commutes with projection to `H¹(Ω¹)`. -/
  hodgeComparison : ∀ z : hodgeSource h 1 2,
    hodgePullback (C.hodgeProjection 1 z) =
      C'.hodgeProjection 1 (dlogPullback z)

namespace Pullback

/-- Build pullback compatibility from three explicit additive maps and their comparison laws. -/
def ofMaps (sq : CommSq f h' h g) (C : ChernClassContext h)
    (C' : ChernClassContext h')
    (dlogPullback : hodgeSource h 1 2 →+ hodgeSource h' 1 2)
    (deRhamPullback : cohomology h 2 →+ cohomology h' 2)
    (hodgePullback : hodgeCohomology h 1 1 →+ hodgeCohomology h' 1 1)
    (dlogNaturality : ∀ x : X.PicardGroup,
      dlogPullback (C.dlogCohomologyMap x) =
        C'.dlogCohomologyMap (Scheme.Hom.picardPullback f x))
    (deRhamComparison : ∀ z : hodgeSource h 1 2,
      deRhamPullback ((hodgeMap h 1 2).hom z) =
        (hodgeMap h' 1 2).hom (dlogPullback z))
    (hodgeComparison : ∀ z : hodgeSource h 1 2,
      hodgePullback (C.hodgeProjection 1 z) =
        C'.hodgeProjection 1 (dlogPullback z)) :
    Pullback sq C C' where
  dlogPullback := dlogPullback
  deRhamPullback := deRhamPullback
  hodgePullback := hodgePullback
  dlogNaturality := dlogNaturality
  deRhamComparison := deRhamComparison
  hodgeComparison := hodgeComparison

/-- The three defining comparison equations for pullback compatibility. -/
theorem spec (sq : CommSq f h' h g) (C : ChernClassContext h)
    (C' : ChernClassContext h') (P : Pullback sq C C') (x : X.PicardGroup)
    (z : hodgeSource h 1 2) :
    (P.dlogPullback (C.dlogCohomologyMap x) =
      C'.dlogCohomologyMap (Scheme.Hom.picardPullback f x)) ∧
    (P.deRhamPullback ((hodgeMap h 1 2).hom z) =
      (hodgeMap h' 1 2).hom (P.dlogPullback z)) ∧
    P.hodgePullback (C.hodgeProjection 1 z) =
      C'.hodgeProjection 1 (P.dlogPullback z) := sorry

end Pullback

/-- Pullback along a commutative square of schemes commutes with the de Rham first Chern
class map. -/
theorem deRhamFirstChern_naturality (sq : CommSq f h' h g)
    (C : ChernClassContext h) (C' : ChernClassContext h')
    (P : Pullback sq C C') :
    P.deRhamPullback.comp C.deRhamFirstChern =
      C'.deRhamFirstChern.comp (Scheme.Hom.picardPullback f) := sorry

/-- Pullback along a commutative square of schemes commutes with the Hodge first Chern
class map. -/
theorem hodgeFirstChern_naturality (sq : CommSq f h' h g)
    (C : ChernClassContext h) (C' : ChernClassContext h')
    (P : Pullback sq C C') :
    P.hodgePullback.comp C.hodgeFirstChern =
      C'.hodgeFirstChern.comp (Scheme.Hom.picardPullback f) := sorry

/-- Pointwise form of de Rham first-Chern pullback naturality. -/
theorem deRhamFirstChern_naturality_apply (sq : CommSq f h' h g)
    (C : ChernClassContext h) (C' : ChernClassContext h')
    (P : Pullback sq C C') (x : X.PicardGroup) :
    P.deRhamPullback (C.deRhamFirstChern x) =
      C'.deRhamFirstChern (Scheme.Hom.picardPullback f x) := sorry

/-- Pointwise form of Hodge first-Chern pullback naturality. -/
theorem hodgeFirstChern_naturality_apply (sq : CommSq f h' h g)
    (C : ChernClassContext h) (C' : ChernClassContext h')
    (P : Pullback sq C C') (x : X.PicardGroup) :
    P.hodgePullback (C.hodgeFirstChern x) =
      C'.hodgeFirstChern (Scheme.Hom.picardPullback f x) := sorry

end ChernClassContext

end AlgebraicGeometry.Scheme.DeRham
