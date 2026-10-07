module

public import Mathlib.CategoryTheory.EqToHom
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Outer projection from an iterated categorical pullback

This leaf owns the generalized cospan transformation, the resulting outer-projection functor, and
its two projection isomorphisms.  Their observable formulas live in `OuterProjection.Computations`.
-/

@[expose] public section

open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]
variable {F : Type u₆} [Category.{v₆} F]

namespace Limits.CategoricalPullback

variable (AB : A ⥤ B) (ED : E ⥤ D)
variable {CB : C ⥤ B} {CD : C ⥤ D} {BF : B ⥤ F} {DF : D ⥤ F}

namespace OuterProjection

/- The natural `2`-categorical input is an invertible cell
`comm : CB ⋙ BF ≅ CD ⋙ DF`, not an equality of functors. It determines the vertical map
of cospans

```
                              (π₂ AB CB) ⋙ CD                              ED
       AB ⊡ CB ─────────────────────────────────────▶ D ◀──────────────────────────── E
          │                                              │                              │
 π₁ AB CB │                                           DF │                          𝟭 E │
          ▼                                              ▼                              ▼
          A ───────────────────────────────────────────▶ F ◀──────────────────────────── E
                                  AB ⋙ BF                              ED ⋙ DF
```

The left square first uses `comm.symm` to move from the `D` route to the `B` route and then the
inverse structural square of `AB ⊡ CB`. The source's strict commutativity hypothesis is promoted
to this cell with `eqToIso`; keeping that specialization only at the tagged declaration preserves
the literal source while the owner remains reusable in genuinely `2`-commutative diagrams.

No public notation is introduced: an operator would still have to display six functors and the
comparison cell, while `OuterProjection.ofIso` states which two entries are retained. -/

/-- The left comparison isomorphism used to assemble the outer-projection cospan
transformation. -/
def transform.leftIso (comm : CB ⋙ BF ≅ CD ⋙ DF) :
    π₂ AB CB ⋙ CD ⋙ DF ≅ π₁ AB CB ⋙ AB ⋙ BF :=
  Functor.associator (π₂ AB CB) CD DF ≪≫
    Functor.isoWhiskerLeft (π₂ AB CB) comm.symm ≪≫
    (Functor.associator (π₂ AB CB) CB BF).symm ≪≫
    Functor.isoWhiskerRight (catCommSq AB CB).iso.symm BF ≪≫
    Functor.associator (π₁ AB CB) AB BF

/-- The reusable cospan transformation underlying projection from an iterated categorical
pullback to its two outer entries. -/
def transform (comm : CB ⋙ BF ≅ CD ⋙ DF) :
    CatCospanTransform ((π₂ AB CB) ⋙ CD) ED (AB ⋙ BF) (ED ⋙ DF) where
  left := π₁ AB CB
  base := DF
  right := (𝟭 E : E ⥤ E)
  squareLeft := ⟨transform.leftIso AB comm⟩
  squareRight := ⟨(Functor.leftUnitor (ED ⋙ DF)).symm⟩

/-- The canonical projection from an iterated categorical pullback to its two outer entries,
associated to an invertible comparison `comm : CB ⋙ BF ≅ CD ⋙ DF`:

`((π₂ AB CB ⋙ CD) ⊡ ED) ⥤ (AB ⋙ BF) ⊡ (ED ⋙ DF)`.

On objects it sends `((a, c, φ), e, ψ)` to `(a, e, θ)`, where `θ` is the composite of
`BF.mapIso φ`, `comm.app c`, and `DF.mapIso ψ`. This formulation is reusable for genuinely
`2`-commutative diagrams. -/
def ofIso (comm : CB ⋙ BF ≅ CD ⋙ DF) :
    ((π₂ AB CB) ⋙ CD) ⊡ ED ⥤ (AB ⋙ BF) ⊡ (ED ⋙ DF) :=
  map (transform AB ED comm)

/-- Lemma 4.31.9 (Stacks 04S7): if the two routes from `C` to `F` commute strictly,
`hcomm : CB ⋙ BF = CD ⋙ DF`, there is a canonical outer projection. This is the source-facing
specialization of `OuterProjection.ofIso` along `eqToIso hcomm`; its object formula is therefore
`BF.mapIso φ ≪≫ (eqToIso hcomm).app c ≪≫ DF.mapIso ψ`. -/
@[stacks 04S7 "outer projection of an iterated categorical pullback"]
def ofEq (hcomm : CB ⋙ BF = CD ⋙ DF) :
    ((π₂ AB CB) ⋙ CD) ⊡ ED ⥤ (AB ⋙ BF) ⊡ (ED ⋙ DF) :=
  ofIso AB ED (eqToIso hcomm)

namespace ofIso

/-- Projecting the generalized outer projection to `A` recovers the two successive first
projections. -/
def fstIso (comm : CB ⋙ BF ≅ CD ⋙ DF) :
    ofIso AB ED comm ⋙ π₁ (AB ⋙ BF) (ED ⋙ DF) ≅
      π₁ ((π₂ AB CB) ⋙ CD) ED ⋙ π₁ AB CB :=
  mapFstIso (transform AB ED comm)

/-- Projecting the generalized outer projection to `E` recovers the source's second
projection. -/
def sndIso (comm : CB ⋙ BF ≅ CD ⋙ DF) :
    ofIso AB ED comm ⋙ π₂ (AB ⋙ BF) (ED ⋙ DF) ≅
      π₂ ((π₂ AB CB) ⋙ CD) ED :=
  mapSndIso (transform AB ED comm) ≪≫ Functor.rightUnitor _

end ofIso

end OuterProjection

end Limits.CategoricalPullback

end CategoryTheory
