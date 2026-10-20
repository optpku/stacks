module

public import ReasLib.Topology.Algebra.OpenMapping
public import ReasLib.Topology.Catenary
public import ReasLib.Topology.Bases
public import ReasLib.Topology.Category
public import ReasLib.Topology.ClosedPoints
public import ReasLib.Topology.Cofinite
public import ReasLib.Topology.Compactness
public import ReasLib.Topology.CompactOpen
public import ReasLib.Topology.Compactification.StoneCech
public import ReasLib.Topology.ConnectedComponents
public import ReasLib.Topology.Counterexamples
public import ReasLib.Topology.Constructible
public import ReasLib.Topology.ConstructibleTopology
public import ReasLib.Topology.Discrete
public import ReasLib.Topology.ExtremallyDisconnected
public import ReasLib.Topology.Indiscrete
public import ReasLib.Topology.IrreducibleCloseds
public import ReasLib.Topology.IrreducibleComponents
public import ReasLib.Topology.Jacobson
public import ReasLib.Topology.KrullDimension
public import ReasLib.Topology.LocallyClosed
public import ReasLib.Topology.Maps
public import ReasLib.Topology.Noetherian
public import ReasLib.Topology.NowhereDense
public import ReasLib.Topology.Opens
public import ReasLib.Topology.Order.LowerSet.PNat
public import ReasLib.Topology.Presheaf
public import ReasLib.Topology.Separation.Cardinal
public import ReasLib.Topology.Sheaf
public import ReasLib.Topology.OpenCover
public import ReasLib.Topology.Shrinking
public import ReasLib.Topology.Sierpinski
public import ReasLib.Topology.Sober
public import ReasLib.Topology.Specialization
public import ReasLib.Topology.Spectral
public import ReasLib.Topology.Stratification
public import ReasLib.Topology.Sum

/-!
# Topology infrastructure library

Top-level entry point for the topology infrastructure used by the Stacks Project formalization.
This library extends Mathlib's topology/sheaves API with constructions needed for algebraic
geometry.

## Organization

- `Opens`: pure topology of open subsets (inclusions, subspace representation, section comparison)
- `Presheaf`: presheaf-level constructions (extension by initial, filtered stalks)
- `Sheaf`: sheaf-level constructions (basis sheaves, gluing, subset pushforward, flasque, etc.)
- `OpenCover`: topological open covers
- `Counterexamples`: reusable topological and sheaf-theoretic counterexamples
- `Shrinking`: compact-subset and tuplewise shrinking of open families
- `Compactness`: compact Hausdorff, closed-point, and Alexander-subbase extensions
- `ConnectedComponents`: clopen descriptions and map/fiber APIs for connected components
- `Category`: categorical API for `TopCat`, profinite and Stonean spaces, topological groups,
  and topological commutative rings
- `ClosedPoints`: specialization criteria and homeomorphism transport for closed points
- `Maps`: equality loci, spectral ranges, and open/closed quotient-map transport
- `LocallyClosed` and `Constructible`: finite decompositions and irreducible-trace criteria
- `ConstructibleTopology`, `Jacobson`, and `NowhereDense`: patch topology, closed-point traces,
  and local nowhere-dense API
- `IrreducibleCloseds` and `Sober`: soberification and Kolmogorov reflection
- `Noetherian`, `Catenary`, `KrullDimension`, `Specialization`: dimension infrastructure
- `CompactOpen` and `Spectral`: compact-open diagrams and spectral-space applications
- `Stratification`, `ExtremallyDisconnected`, `Cofinite`, `Sierpinski`, and `Sum`: reusable
  decomposition, compactification, and counterexample infrastructure

## Import guide

- For open-subset infrastructure: `import ReasLib.Topology.Opens`
- For all category-level topology infrastructure: `import ReasLib.Topology.Category`
- For `TopCat` only: `import ReasLib.Topology.Category.TopCat`
- For profinite-space recognition: `import ReasLib.Topology.Category.Profinite.Recognition`
- For profinite-group finite-limit presentations:
  `import ReasLib.Topology.Category.ProfiniteGrp.Recognition`
- For Stonean lifts and minimal-cover comparisons:
  `import ReasLib.Topology.Category.Stonean`
- For topological groups: `import ReasLib.Topology.Category.GrpTopCat`
- For topological commutative rings: `import ReasLib.Topology.Category.TopCommRingCat`
- For presheaf extension by initial (`jₚ!`): `import ReasLib.Topology.Presheaf.ExtensionByInitial`
- For sheaf extension by initial (`j!`): `import ReasLib.Topology.Sheaf.ExtensionByInitial`
- For coefficient-independent open-subspace restriction: `import ReasLib.Topology.Sheaf.OpenSubset`
- For basis sheaves: `import ReasLib.Topology.Sheaf.OnBasis`
- For gluing/descent: `import ReasLib.Topology.Sheaf.Gluing`
- For filter-germ maps from type-valued stalks: `import ReasLib.Topology.Sheaves.Types.FilterGerm`
- For the two-closed-points tail-sheaf counterexample:
  `import ReasLib.Topology.Counterexamples.TwoClosedPoints`
- For subset pushforward: `import ReasLib.Topology.Sheaf.Subset`
- For quotient-map subset transport: `import ReasLib.Topology.Maps.OpenQuotient`
- For retrocompact ranges of spectral maps: `import ReasLib.Topology.Maps.Spectral`
- For compact-space closed points: `import ReasLib.Topology.Compactness.ClosedPoints`
- For Alexander finite-refinement subbasis arguments: `import ReasLib.Topology.Compactness.Alexander`
- For clopen descriptions of connected components:
  `import ReasLib.Topology.ConnectedComponents.Clopen`
- For tuplewise shrinking of compact open covers: `import ReasLib.Topology.Shrinking`
- For the common tuple-controlled cover condition:
  `import ReasLib.Topology.Shrinking.Controlled`
- For prescribed finite intersections in a shrinking:
  `import ReasLib.Topology.Shrinking.PrescribedIntersections`
- For compact-open cover-refinement data:
  `import ReasLib.Topology.CompactOpen.Refinement`
- For constructible unions of locally closed subsets:
  `import ReasLib.Topology.Constructible.LocallyClosedUnion`
- For arbitrary or finite unions of locally closed subsets:
  `import ReasLib.Topology.LocallyClosed.Union.Basic` or
  `import ReasLib.Topology.LocallyClosed.Union.Finite`
- For constructible-topology and spectral-space criteria:
  `import ReasLib.Topology.ConstructibleTopology.Spectral`
- For local Noetherianity and its transport API: `import ReasLib.Topology.Noetherian.Basic`
- For closed-point traces in locally constructible subsets:
  `import ReasLib.Topology.Jacobson.LocallyConstructible`
- For closed-point trace equivalence factories:
  `import ReasLib.Topology.Jacobson.ClosedPoints` or
  `import ReasLib.Topology.Jacobson.Constructible`
- For stable-subset diagrams:
  `import ReasLib.Topology.Category.TopCat.StableSubset`
- For open and compact-open descent along a cofiltered limit:
  `import ReasLib.Topology.Category.TopCat.Limits.Cofiltered`
- For recognizing a `TopCat` limit from its underlying type cone and a preimage basis:
  `import ReasLib.Topology.Category.TopCat.Limits.Recognition`
- For compactness of an arbitrary compact Hausdorff limiting cone:
  `import ReasLib.Topology.Category.TopCat.Limits.Compact`
- For finite good stratification refinements:
  `import ReasLib.Topology.Stratification.Refinement`
- For the order structure on open normal subgroups:
  `import ReasLib.Topology.Algebra.OpenNormalSubgroup`
- For constructible stability: `import ReasLib.Topology.Constructible.Specialization`
- For dimension-function catenarity and local existence: `import ReasLib.Topology.Specialization.Dimension.Catenary`
- For soberification: `import ReasLib.Topology.Sober.Soberification`
- For compact-open intersection limits: `import ReasLib.Topology.CompactOpen.Intersection`
- For everything: `import ReasLib.Topology`
-/
