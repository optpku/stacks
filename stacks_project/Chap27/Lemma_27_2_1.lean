/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.Basic
import StacksCheckRecall

/-!
# Lemma 27.2.1 compatibility entry point

The reusable basis-indexed scheme gluing datum, realization predicate, and
existence and uniqueness statements are owned by
`ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.Basic`.
-/

@[expose] public section

universe u v

/- The reusable datum records the source basis, local schemes, transition morphisms, pullback
conditions, and cocycle. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} :
    AlgebraicGeometry.Scheme.{u} → Type (max (u + 1) (v + 1)))

/- Each local structure morphism composes with its basis-open inclusion to the ambient base. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.localToBase :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S) (i : D.ι),
      D.X i ⟶ S)

/- The consumer predicate records realization by compatible local identifications. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realizes :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S)
      {X : AlgebraicGeometry.Scheme.{u}},
      (X ⟶ S) → Prop)

/- An equipped realization retains the global scheme, its morphism to the base, and all chosen
local identifications. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S → Type (max (u + 1) v))

/- Forgetting the equipped fields gives the source realization predicate. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization.realizes :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S)
      (R : AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization D),
      AlgebraicGeometry.Scheme.BasisSchemeGluing.Realizes D R.toBase)

/- Equipped realizations are compared by global and local compatible isomorphisms. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.RealizationIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S)
      (R R' : AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization D),
      Type (max u v))

/- The companion projection exposes the underlying global morphism of a realization
isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.RealizationIso.hom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {D : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S}
      {R R' : AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization D},
      AlgebraicGeometry.Scheme.BasisSchemeGluing.RealizationIso D R R' → (R.Y ⟶ R'.Y))

/- Lemma 27.2.1: pullback-compatible schemes over a basis glue to an equipped scheme over the
base. -/
@[stacks 01LH] #check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization.nonempty :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S),
      Nonempty (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization D))

/- The equipped realization is unique up to a unique isomorphism over the base that intertwines
all chosen local identifications. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization.existsUniqueIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (D : AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} S)
      (R R' : AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization D),
      ∃ e : AlgebraicGeometry.Scheme.BasisSchemeGluing.RealizationIso D R R',
        ∀ e' : AlgebraicGeometry.Scheme.BasisSchemeGluing.RealizationIso D R R', e' = e)
