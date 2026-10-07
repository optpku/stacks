module

public import ReasLib.Algebra.CentralSimple.Basic
public import ReasLib.Algebra.CentralSimple.TwoSidedSubmodule
public import ReasLib.Algebra.CentralSimple.TensorProduct
public import ReasLib.Algebra.CentralSimple.BaseChange
public import ReasLib.Algebra.CentralSimple.BrauerGroup.Group
public import ReasLib.Algebra.CentralSimple.Azumaya
public import ReasLib.Algebra.CentralSimple.SimpleModule.SimpleModule
public import ReasLib.Algebra.CentralSimple.BrauerGroup.BrauerGroup
public import ReasLib.Algebra.CentralSimple.SkolemNoether
public import ReasLib.Algebra.CentralSimple.Centralizer.Centralizer
public import ReasLib.Algebra.CentralSimple.Splitting.Splitting

/-! # Central Simple Algebras

This is the top-level aggregator for the shared library on central simple algebras
and the Brauer group. Import this file to get the full API, or import individual
sub-modules for finer-grained dependency control.

## Sub-modules

- `Basic` — centrality transfer lemmas
- `TwoSidedSubmodule` — bimodule descent for K ⊗ V
- `TensorProduct` — tensor product of CSAs is CSA
- `BaseChange` — scalar extension of CSAs
- `Opposite` — opposite CSA, A ⊗ Aᵒᵖ ≅ Mₙ(k)
- `Azumaya` — CSA ⟹ IsAzumaya
- `SimpleModule/` — simple module theory over simple rings
- `BrauerGroup/` — CommGroup instance and properties
- `SkolemNoether` — the Skolem-Noether theorem
- `Centralizer/` — centralizer theory in CSAs
- `Splitting/` — splitting fields
-/
