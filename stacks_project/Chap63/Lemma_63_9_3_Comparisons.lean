/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap63.Lemma_63_9_2_Comparison
public import stacks_project.Chap63.Lemma_63_9_3_Compactification

/-! The four specified composition comparisons of the compactification tower.
Only their geometric arguments are specialized here. Remaining sheafification,
localization, Kan extension and exactness inputs are exactly the canonical
composition construction's technical parameters. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification
noncomputable section
universe u v

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.Associativity

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T] (A : AssocDiagram X g h)

/-- The actual composition comparison for rectangle A. -/
def gammaA :=
  @comp.{u, v, v, v, v, v, v} Y Z X g inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (AssocDiagram.compFG X g h A)

/-- The actual composition comparison for rectangle C. -/
def gammaC :=
  @comp.{u, v, v, v, v, v, v} Z T (Over.mk g) h inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (AssocDiagram.compHG X g h A)

/-- The A+B comparison retains its right-associated compactification codomain. -/
def gammaAB :=
  @comp.{u, v, v, v, v, v, v} Y T X (g ≫ h) inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (AssocDiagram.compF X g h A)

/-- The B+C comparison retains its left-associated compactification codomain. -/
def gammaBC :=
  @comp.{u, v, v, v, v, v, v} Z T (Over.mk (X.hom ≫ g)) h inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (AssocDiagram.compH X g h A)

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.Associativity
end
