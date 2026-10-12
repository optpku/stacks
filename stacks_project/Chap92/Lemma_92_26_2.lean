/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_26_2_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Étale localization of the cotangent complex of algebraic spaces

Lemma 92.26.2 identifies the restriction of `L_{X/Y}` along an étale morphism
`p : U ⟶ X` with `L_{U/V}` in `D(O_U)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

noncomputable section

universe u

/-- Lemma 92.26.2. Let `S` be a scheme. Consider a commutative diagram of algebraic
spaces over `S` with `p : U ⟶ X` and `q : V ⟶ Y` étale. Then there is a canonical
identification `pullbackCotangent p f ≅ cotangent g` in `DerivedCategory (CommModules U)`. -/
@[stacks 08VE]
abbrev etaleRestrictIso {S : Scheme.{u}} {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale p] [Etale q] (sq : CommSq g p q f) :
    Cotangent.pullbackCotangent p f ≅ Cotangent.cotangent g :=
  Cotangent.etaleRestrictIso p q g f sq

/-- The source-facing identification is `DerivedCategory.Q.mapIso` of
`etaleRestrictCochainIso`. -/
theorem etaleRestrictIso_eq {S : Scheme.{u}} {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale p] [Etale q] (sq : CommSq g p q f) :
    etaleRestrictIso p q g f sq =
      DerivedCategory.Q.mapIso (Cotangent.etaleRestrictCochainIso p q g f sq) :=
  sorry
