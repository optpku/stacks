/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Left-leg diagonal squares

This module owns the ordinary categorical constructions induced by the left leg of a
categorical commutative square. The categories may have independent object and morphism
universes; the fixed-universe `Pith Cat` bilimit statement lives in `LeftLegDiagonal.Bilimit`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe vU vX vV vY uU uX uV uY

noncomputable section

namespace CategoricalPullback.CatCommSqOver

variable {U : Type uU} [Category.{vU} U]
variable {X : Type uX} [Category.{vX} X]
variable {V : Type uV} [Category.{vV} V]
variable {Y : Type uY} [Category.{vY} Y]
variable {F : X ⥤ Y} {G : V ⥤ Y}

namespace LeftLegDiagonal

/-- The cospan transformation induced by the left vertical leg of `P`:

```
                         P.snd                                  P.snd
       U ───────────────────────────────▶ V ◀────────────────────────────── U
       │                                  │                                │
 P.fst │                                G │                          P.fst │
       ▼                                  ▼                                ▼
       X ───────────────────────────────▶ Y ◀────────────────────────────── X
                          F                                      F
```

Both comparison cells are `P.iso.symm`. -/
def transform (P : CatCommSqOver F G U) :
    CatCospanTransform P.snd P.snd F F :=
  CatCospanTransform.ofIso P.iso.symm P.iso.symm

/-- The left leg of `P` induces the functor from the self-pullback of `P.snd` to the
self-pullback of `F`. -/
def map (P : CatCommSqOver F G U) :
    P.snd ⊡ P.snd ⥤ F ⊡ F :=
  CategoricalPullback.map (transform P)

namespace map

/-- The map induced by the left leg commutes with the first pullback projection. -/
def fstIso (P : CatCommSqOver F G U) :
    LeftLegDiagonal.map P ⋙ π₁ F F ≅ π₁ P.snd P.snd ⋙ P.fst :=
  mapFstIso (transform P)

/-- The map induced by the left leg commutes with the second pullback projection. -/
def sndIso (P : CatCommSqOver F G U) :
    LeftLegDiagonal.map P ⋙ π₂ F F ≅ π₂ P.snd P.snd ⋙ P.fst :=
  mapSndIso (transform P)

end map

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace iso.Implementation

/-- Coherence of the two projected isomorphisms defining the diagonal comparison attached to
the left leg of `P`. -/
private theorem coherence (P : CatCommSqOver F G U) :
    Functor.whiskerRight (Functor.isoWhiskerLeft (Δₚ P.snd)
      (map.fstIso P)).hom F ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (P.fst ⋙ Δₚ F)
          (CatCommSq.iso (π₁ F F) (π₂ F F) F F).hom ≫
        (Functor.associator _ _ _).inv =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (Δₚ P.snd ⋙ LeftLegDiagonal.map P)
          (CatCommSq.iso (π₁ F F) (π₂ F F) F F).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.isoWhiskerLeft (Δₚ P.snd)
          (map.sndIso P)).hom F := sorry

end iso.Implementation

/-- The comparison isomorphism making the square induced by the left leg of `P`
`2`-commutative. -/
def iso (P : CatCommSqOver F G U) :
    Δₚ P.snd ⋙ LeftLegDiagonal.map P ≅ P.fst ⋙ Δₚ F :=
  mkNatIso
    (Functor.isoWhiskerLeft (Δₚ P.snd) (map.fstIso P))
    (Functor.isoWhiskerLeft (Δₚ P.snd) (map.sndIso P))
    (iso.Implementation.coherence P)

/-- The diagonal square over the cospan
`U ×[V] U ⥤ X ×[Y] X ← X` attached to the left leg of `P`. -/
@[stacks 04YR "left-leg diagonal pullback square"]
def square (P : CatCommSqOver F G U) :
    CatCommSqOver (LeftLegDiagonal.map P) (Δₚ F) U :=
  { fst := Δₚ P.snd
    snd := P.fst
    iso := LeftLegDiagonal.iso P }

end LeftLegDiagonal

end CategoricalPullback.CatCommSqOver

end

end CategoryTheory.Limits
