module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.PrincipalCohomology
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import ReasLib.Algebra.Homology.Koszul.PowerTower
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import ReasLib.CategoryTheory.Linear.PrincipalPower.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal derived-completion cohomology diagram

This file names the seven objects and the comparison diagram that relate ordinary principal-adic
completion of cohomology to cohomology of principal derived completion.  The four exact sequences
are retained as `ShortComplex` data, while the two derived-limit error terms are connected by the
bottom isomorphism from the source diagram.

The tower index is zero-based: stage `n` uses the two-term Koszul complex on `f ^ (n + 1)`.

@stack 0H32
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem

universe u

-- Local instance justification (defeq pin): use the standard derived-category model uniformly
-- in the completion, tensor-product, and cohomology objects below.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory.PrincipalPower.CohomologyDiagram

variable {A : Type u} [CommRing A]

/-- Degree-`p` cohomology on `D(A)`. -/
@[stacks 0H32 "principal completion cohomology functor"]
abbrev homology (p : ℤ) :
    DerivedCategory (ModuleCat.{u} A) ⥤ ModuleCat.{u} A :=
  DerivedCategory.homologyFunctor (ModuleCat.{u} A) p

/-- The inverse system `K ⊗ᴸ_A K(A; f ^ (n + 1))`. -/
@[stacks 0H32 "principal Koszul tensor tower"]
abbrev koszulTensorSystem (f : A) (K : DerivedCategory (ModuleCat.{u} A)) :
    SequentialInverseSystem (DerivedCategory (ModuleCat.{u} A)) :=
  KoszulComplex.PowerTower.derivedSystem (fun _ : Fin 1 ↦ f) ⋙
    DerivedCategory.derivedTensorProduct K

/-- The ordinary `f`-adic completion of `H^p(K)`, presented as a quotient-system limit. -/
@[stacks 0H32 "comparison diagram top-left object"]
abbrev topLeft (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) :
    ModuleCat.{u} A :=
  limit (ModuleCat.PrincipalPower.quotientSystem f ((homology p).obj K))

/-- The limit of the degree-`p` cohomology system of the principal Koszul tensor tower. -/
@[stacks 0H32 "comparison diagram top-middle object"]
abbrev topMiddle (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) :
    ModuleCat.{u} A :=
  limit (koszulTensorSystem f K ⋙ homology p)

/-- Degree-zero cohomology of the derived completion of `H^p(K)[0]`. -/
@[stacks 0H32 "comparison diagram middle-left object"]
abbrev middleLeft (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) :
    ModuleCat.{u} A :=
  PrincipalCompletion.moduleHomology f ((homology p).obj K) 0

/-- Degree-`p` cohomology of the principal derived completion of `K`. -/
@[stacks 0H32 "comparison diagram middle-middle object"]
abbrev middleMiddle (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) :
    ModuleCat.{u} A :=
  (homology p).obj
    (DerivedCategory.derivedCompletionOf (principalIdeal f) (principalIdeal_fg f) K)

/-- The principal Tate module of `H^(p+1)(K)`, shared by the top and middle rows. -/
@[stacks 0H32 "comparison diagram right object"]
abbrev right (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) :
    ModuleCat.{u} A :=
  ModuleCat.PrincipalPower.tateModule f ((homology (p + 1)).obj K)

/-- The first derived limit of the principal-power torsion system of `H^p(K)`. -/
@[stacks 0H32 "comparison diagram bottom-left object"]
abbrev bottomLeft (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) :
    ModuleCat.{u} A :=
  firstDerivedLimit (ModuleCat.PrincipalPower.torsionSystem f ((homology p).obj K))

/-- The first derived limit of `H^(p-1)` of the principal Koszul tensor tower. -/
@[stacks 0H32 "comparison diagram bottom-middle object"]
abbrev bottomMiddle (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) :
    ModuleCat.{u} A :=
  firstDerivedLimit (koszulTensorSystem f K ⋙ homology (p - 1))

/-- The comparison diagram for principal derived completion in one cohomological degree. -/
@[stacks 0H32 "principal derived-completion cohomology comparison diagram"]
structure Comparison (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) where
  /-- The first map in the top row. -/
  topLeftMap : topLeft f K p ⟶ topMiddle f K p
  /-- The second map in the top row. -/
  topRightMap : topMiddle f K p ⟶ right f K p
  /-- The top-row composite vanishes. -/
  topRowZero : topLeftMap ≫ topRightMap = 0
  /-- The first map in the middle row. -/
  middleLeftMap : middleLeft f K p ⟶ middleMiddle f K p
  /-- The second map in the middle row. -/
  middleRightMap : middleMiddle f K p ⟶ right f K p
  /-- The middle-row composite vanishes. -/
  middleRowZero : middleLeftMap ≫ middleRightMap = 0
  /-- The upper map in the left column. -/
  leftTopMap : topLeft f K p ⟶ middleLeft f K p
  /-- The lower map in the left column. -/
  leftBottomMap : middleLeft f K p ⟶ bottomLeft f K p
  /-- The left-column composite vanishes. -/
  leftColumnZero : leftTopMap ≫ leftBottomMap = 0
  /-- The upper map in the middle column. -/
  middleTopMap : topMiddle f K p ⟶ middleMiddle f K p
  /-- The lower map in the middle column. -/
  middleBottomMap : middleMiddle f K p ⟶ bottomMiddle f K p
  /-- The middle-column composite vanishes. -/
  middleColumnZero : middleTopMap ≫ middleBottomMap = 0
  /-- The bottom comparison between the two first-derived-limit terms. -/
  bottomIso : bottomLeft f K p ≅ bottomMiddle f K p
  /-- The morphism from the top short exact row to the middle short exact row. -/
  topToMiddle :
    ShortComplex.mk topLeftMap topRightMap topRowZero ⟶
      ShortComplex.mk middleLeftMap middleRightMap middleRowZero
  /-- The left component of `topToMiddle` is the upper left-column map. -/
  topToMiddleLeft : topToMiddle.τ₁ = leftTopMap
  /-- The middle component of `topToMiddle` is the upper middle-column map. -/
  topToMiddleMiddle : topToMiddle.τ₂ = middleTopMap
  /-- The right component of `topToMiddle` is the identity of the common Tate term. -/
  topToMiddleRight : topToMiddle.τ₃ = 𝟙 (right f K p)
  /-- The top row is short exact. -/
  topRowShortExact :
    (ShortComplex.mk topLeftMap topRightMap topRowZero).ShortExact
  /-- The middle row is short exact. -/
  middleRowShortExact :
    (ShortComplex.mk middleLeftMap middleRightMap middleRowZero).ShortExact
  /-- The left column is short exact. -/
  leftColumnShortExact :
    (ShortComplex.mk leftTopMap leftBottomMap leftColumnZero).ShortExact
  /-- The middle column is short exact. -/
  middleColumnShortExact :
    (ShortComplex.mk middleTopMap middleBottomMap middleColumnZero).ShortExact
  /-- The bottom square commutes through the bottom comparison isomorphism. -/
  bottomSquare :
    CommSq middleLeftMap leftBottomMap middleBottomMap bottomIso.hom

namespace Comparison

/-- The top short complex of a principal derived-completion comparison diagram. -/
@[stacks 0H32 "top row of the principal completion diagram"]
abbrev topRow {f : A} {K : DerivedCategory (ModuleCat.{u} A)} {p : ℤ}
    (D : Comparison f K p) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk D.topLeftMap D.topRightMap D.topRowZero

/-- The middle short complex of a principal derived-completion comparison diagram. -/
@[stacks 0H32 "middle row of the principal completion diagram"]
abbrev middleRow {f : A} {K : DerivedCategory (ModuleCat.{u} A)} {p : ℤ}
    (D : Comparison f K p) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk D.middleLeftMap D.middleRightMap D.middleRowZero

/-- The left-column short complex of a principal derived-completion comparison diagram. -/
@[stacks 0H32 "left column of the principal completion diagram"]
abbrev leftColumn {f : A} {K : DerivedCategory (ModuleCat.{u} A)} {p : ℤ}
    (D : Comparison f K p) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk D.leftTopMap D.leftBottomMap D.leftColumnZero

/-- The middle-column short complex of a principal derived-completion comparison diagram. -/
@[stacks 0H32 "middle column of the principal completion diagram"]
abbrev middleColumn {f : A} {K : DerivedCategory (ModuleCat.{u} A)} {p : ℤ}
    (D : Comparison f K p) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk D.middleTopMap D.middleBottomMap D.middleColumnZero

/-- The bundled source specification: both rows and both columns are short exact, the row
comparison uses the two column maps and the identity on the Tate term, and the bottom square
commutes through the chosen isomorphism. -/
@[stacks 0H32 "principal completion comparison diagram specification"]
theorem spec {f : A} {K : DerivedCategory (ModuleCat.{u} A)} {p : ℤ}
    (D : Comparison f K p) :
    D.topRow.ShortExact ∧ D.middleRow.ShortExact ∧
      D.leftColumn.ShortExact ∧ D.middleColumn.ShortExact ∧
      D.topToMiddle.τ₁ = D.leftColumn.f ∧
      D.topToMiddle.τ₂ = D.middleColumn.f ∧
      D.topToMiddle.τ₃ = 𝟙 (right f K p) ∧
      CommSq D.middleRow.f D.leftColumn.g D.middleColumn.g D.bottomIso.hom := sorry

end Comparison

/-- Lemma 15.95.6 (Stacks `0H32`): for every `p : ℤ`, the ordinary `f`-adic completion
of `H^p(K)`, the cohomology of the principal derived completion of `K`, and their two Milnor
error terms fit into the comparison diagram with short exact top and middle rows, short exact
left and middle columns, identity right edge, and an isomorphism along the bottom. -/
@[stacks 0H32]
theorem existsComparison (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) :
    Nonempty (Comparison f K p) := sorry

end CategoryTheory.DerivedCategory.PrincipalPower.CohomologyDiagram
