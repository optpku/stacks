/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Smooth
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

@[expose] public section

universe u

/- Lemma 37.19.3 (Normalization and smooth morphisms) (1): a smooth morphism
preserves finiteness of irreducible components on quasi-compact opens. -/
@[stacks 07TD] #check
  (AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
      [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y],
      Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X)

/- Lemma 37.19.3 (Normalization and smooth morphisms) (2): for a smooth
morphism, the normalization of the source is uniquely isomorphic over the
source to the pullback of the normalization of the target. -/
@[stacks 07TD] #check
  (AlgebraicGeometry.Scheme.Normalization.existsUniquePullbackIsoOfSmooth :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
      [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y],
      -- Local instance justification (proof-local temporary data): needed only to form X.normalization in this complete expected type.
      letI : Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X :=
        Scheme.HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth f
      ∃! e : X.normalization ≅ pullback Y.normalizationTo f,
        e.hom ≫ pullback.snd Y.normalizationTo f = X.normalizationTo)
