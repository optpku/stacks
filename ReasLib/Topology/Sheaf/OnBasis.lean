module

public import ReasLib.Topology.Sheaves.Basis.Basic
public import ReasLib.Topology.Sheaves.Basis.Cover
public import ReasLib.Topology.Sheaves.Basis.SheafCondition
public import ReasLib.Topology.Sheaves.Basis.Comparison
public import ReasLib.Topology.Sheaves.Basis.Extension
public import ReasLib.Topology.Sheaves.Basis.Neighborhoods
public import ReasLib.Topology.Sheaves.Basis.Cofinal
public import ReasLib.Topology.Sheaves.Basis.SectionFamilies
public import ReasLib.Topology.Sheaves.Basis.Stalks

/-!
# Sheaves on a topological basis

Canonical entry point for the basis-sheaf theory. Imports and re-exports:
- `BasisOpen`, `basisOpenInclusion` — the full subcategory of basis opens
- `BasisCover`, `BasisIntersectionCover`, `IsBasisSheaf` — the explicit sheaf condition
- `basisGrothendieckTopology`, `BasisSiteSheaf` — site-theoretic formulation
- `isBasisSheaf_iff_isSheaf` — comparison theorem
- `basisSiteSheafComparisonEquiv` — equivalence `Sh(B) ≌ Sh(X)`
- Extension, restriction, stalks, neighborhoods, cofinal systems
-/
