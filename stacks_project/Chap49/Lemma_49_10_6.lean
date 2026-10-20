/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalPolynomialSystem.Properties
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace UniversalPolynomialSystem

/- Lemma 49.10.6 (1): the coefficient scheme `X_(n,d)` is regular. -/
@[stacks 0FK9] #check
  (UniversalPolynomialSystem.baseScheme_regular :
    ∀ (n d : ℕ+), Scheme.Regular (UniversalPolynomialSystem.baseScheme n d))

/- Lemma 49.10.6 (2): the coefficient scheme `X_(n,d)` is irreducible. -/
@[stacks 0FK9] #check
  (UniversalPolynomialSystem.baseScheme_irreducible :
    ∀ (n d : ℕ+), IrreducibleSpace (UniversalPolynomialSystem.baseScheme n d))

/- Lemma 49.10.6 (3): the maximal quasi-finite open `Y_(n,d)` is regular. -/
@[stacks 0FK9] #check
  (UniversalPolynomialSystem.quasiFiniteOpen_regular :
    ∀ (n d : ℕ+),
      Scheme.Regular (UniversalPolynomialSystem.quasiFiniteOpen n d).toScheme)

/- Lemma 49.10.6 (4): the maximal quasi-finite open `Y_(n,d)` is irreducible. -/
@[stacks 0FK9] #check
  (UniversalPolynomialSystem.quasiFiniteOpen_irreducible :
    ∀ (n d : ℕ+),
      IrreducibleSpace (UniversalPolynomialSystem.quasiFiniteOpen n d).toScheme)

/- Lemma 49.10.6 (5): the universal morphism `Y_(n,d) ⟶ X_(n,d)` is locally quasi-finite. -/
@[stacks 0FK9] #check
  (UniversalPolynomialSystem.quasiFiniteOpenProjection_locallyQuasiFinite :
    ∀ (n d : ℕ+),
      LocallyQuasiFinite
        ((UniversalPolynomialSystem.quasiFiniteOpen n d).ι ≫
          UniversalPolynomialSystem.projection n d))

/- Lemma 49.10.6 (6): the universal morphism `Y_(n,d) ⟶ X_(n,d)` is syntomic. -/
@[stacks 0FK9] #check
  (UniversalPolynomialSystem.quasiFiniteOpenProjection_syntomic :
    ∀ (n d : ℕ+),
      Syntomic
        ((UniversalPolynomialSystem.quasiFiniteOpen n d).ι ≫
          UniversalPolynomialSystem.projection n d))

/- Lemma 49.10.6 (7): `Y_(n,d)` contains a dense open subscheme on which the universal morphism
to `X_(n,d)` is étale. -/
@[stacks 0FK9] #check
  (UniversalPolynomialSystem.exists_denseOpen_etale :
    ∀ (n d : ℕ+),
      ∃ V : (UniversalPolynomialSystem.quasiFiniteOpen n d).toScheme.Opens,
        Dense (V : Set (UniversalPolynomialSystem.quasiFiniteOpen n d).toScheme) ∧
          Etale
            (V.ι ≫ (UniversalPolynomialSystem.quasiFiniteOpen n d).ι ≫
              UniversalPolynomialSystem.projection n d))

end UniversalPolynomialSystem
