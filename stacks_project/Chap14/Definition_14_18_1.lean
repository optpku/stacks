/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Split.Truncation.FromSimplicial
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Split.Truncation.Restriction
import StacksCheckRecall

/-!
@stack 017P
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
variable {n : ℕ} (X : SimplicialObject.Truncated C n)
variable (Y : SimplicialObject C)

/- Definition 14.18.1 (1): a simplicial object is split when it admits a splitting whose
distinguished maps represent subobjects. -/
@[stacks 017P]
#check (SimplicialObject.IsSplit Y)

/- Definition 14.18.1 (2): the same existence property is available for truncated simplicial
objects. -/
@[stacks 017P]
#check (SimplicialObject.Truncated.IsSplit X)

/- The underlying data owner for a chosen splitting of a simplicial object. -/
#check (SimplicialObject.Splitting Y)

/- The underlying data owner for a chosen splitting of a truncated simplicial object. -/
#check (SimplicialObject.Truncated.Splitting X)

/- A chosen ambient splitting restricts canonically to every truncation. -/
#check SimplicialObject.Splitting.truncation

/- The restriction is functorial for splitting-compatible morphisms. -/
#check SimplicialObject.Split.truncation

/- A chosen truncated splitting restricts canonically along every comparison `m ≤ n`. -/
#check SimplicialObject.Truncated.Splitting.trunc

/- Further truncation is functorial on bundled split truncated simplicial objects. -/
#check SimplicialObject.Truncated.Split.trunc

/- Direct ambient truncation agrees naturally with truncation through an intermediate level. -/
#check SimplicialObject.Split.truncation.compIso
