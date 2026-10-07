module

public import ReasLib.Topology.Sheaf.Subset
public import ReasLib.Topology.Sheaf.OnBasis
public import ReasLib.Topology.Sheaf.Gluing
public import ReasLib.Topology.Sheaf.Pullback
public import ReasLib.Topology.Sheaf.OpenSubset
public import ReasLib.Topology.Sheaf.OpenClosed
public import ReasLib.Topology.Sheaf.Pushforward
public import ReasLib.Topology.Sheaf.HigherDirectImage
public import ReasLib.Topology.Sheaf.Types
public import ReasLib.Topology.Sheaf.Torsor
public import ReasLib.Topology.Sheaf.Zero
public import ReasLib.Topology.Sheaf.Algebraic
public import ReasLib.Topology.Sheaf.ExtensionByInitial.Presentation
public import ReasLib.Topology.Sheaf.Flasque
public import ReasLib.Topology.Sheaf.Presentation
public import ReasLib.Topology.Sheaf.InverseLimit
public import ReasLib.Topology.Sheaf.Pointwise
public import ReasLib.Topology.Sheaf.ContinuousFunctions
public import ReasLib.Topology.Sheaf.Constructible.FinitePresentation
public import ReasLib.Topology.Sheaf.Ring
public import ReasLib.Topology.Sheaf.Support
public import ReasLib.Topology.Sheaf.Support.ClosedSubset
public import ReasLib.Topology.Sheaf.Skyscraper
public import ReasLib.Topology.Sheaf.Abelian
public import ReasLib.Topology.Sheaf.Cohomology.Bridge
public import ReasLib.Topology.Sheaf.Cohomology.Cech
public import ReasLib.Topology.Sheaf.Cohomology.CompactOpen
public import ReasLib.Topology.Sheaf.Cohomology.CompactSubset
public import ReasLib.Topology.Sheaf.Cohomology.InverseLimit
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
public import ReasLib.Topology.Sheaf.Cohomology.Restriction
public import ReasLib.Topology.Sheaf.Cohomology.Spectral
public import ReasLib.Topology.Sheaf.Cohomology.SpecializingPreimage
public import ReasLib.Topology.Sheaf.HigherDirectImage.Presheaf
public import ReasLib.Topology.Sheaf.HigherDirectImage.Stalk
public import ReasLib.Topology.Sheaf.Cohomology.ClosedEmbedding
public import ReasLib.Topology.Sheaf.Cohomology.Profinite
public import ReasLib.Topology.Sheaf.GlobalSections.Profinite
public import ReasLib.Topology.Sheaf.GlobalSections
public import ReasLib.Topology.Sheaf.LocallySurjective
public import ReasLib.Topology.Sheaf.Forget
public import ReasLib.Topology.Sheaf.Limits
public import ReasLib.Topology.Sheaf.SheafCondition
public import ReasLib.Topology.Sheaf.Notation

/-!
# Sheaf-level constructions on topological spaces

This module aggregates the sheaf-level API for topological spaces.
The organization follows mathematical ownership:

- `Subset/`: pushforward along subset inclusions, fully faithful embedding, stalk vanishing
- `OnBasis`: sheaves on a topological basis (condition, comparison, extension, stalks)
- `Gluing`: descent data and gluing along open covers
- `Pullback`: pullback composition coherence
- `OpenSubset`: coefficient-independent restriction to open subspaces
- `OpenClosed`: the functorial short exact sequence for an open subset and its closed complement
- `Pushforward`: section-level description of pushforward
- `HigherDirectImage`: right-derived pushforward of sheaves of abelian groups
- `Types`: type-valued sheaf specifics
- `Torsor`: local-section and neighborhood APIs for torsors on topological spaces
- `Zero`: canonical zero morphisms for sheaves valued in a category with zero morphisms
- `Algebraic`: algebraic-structure-valued sheaves
- `ExtensionByInitial`: extension by an initial object along open subspace inclusions
- `Flasque`: flasque sheaf extensions
- `Presentation`: finite presentations relative to a compact topological basis
- `InverseLimit`: sheaf systems on inverse limits
- `Pointwise`: pointwise products and direct sums
- `ContinuousFunctions`: sheaves of continuous functions
- `Constructible/FinitePresentation`: constructible embeddings of finite compact-open presentations
- `Ring`: sheaves of rings
- `Support`: support of additive and ring sheaves
- `Support/ClosedSubset`: coefficient-generic kernel-model support, with additive and pointed
  functoriality and closed-subset pushforward adjunctions
- `Skyscraper`: skyscraper sheaves
- `Abelian`: abelian structure on sheaf categories
- `Cohomology/CompactOpen`: canonical cohomology comparisons for compact-open intersections,
  their differences, and compact-open neighbourhood systems
- `Cohomology/CompactSubset`: cohomology over open neighbourhoods of a compact subset
- `Cohomology/InverseLimit`: cohomology comparison for compatible sheaves on inverse systems
- `Cohomology/Restriction`: canonical restriction maps between open-set cohomology objects
- `Cohomology/Spectral`: Krull-dimension bounds for ordinary and supported cohomology on spectral
  spaces
- `Cohomology/SpecializingPreimage`: the canonical neighbourhood-colimit comparison with
  cohomology on the inverse image of a point's specializing locus
- `HigherDirectImage/Presheaf`: the canonical presheaf comparison underlying higher direct images
- `HigherDirectImage/Stalk`: the canonical higher-direct-image stalk comparison, including its
  stage formula and coefficient naturality
- `Cohomology/ClosedEmbedding`: exact direct image and all-degree cohomology comparison for
  closed embeddings
- `Cohomology/Profinite`: exact global sections and positive-degree cohomology vanishing on
  profinite spaces
- `GlobalSections/Profinite`: exactness and canonical finite-colimit/homology-preservation
  instances for both top-open evaluation and `Sheaf.Γ`
- `Notation`: the standard set-valued `PSh(X)` and `Sh(X)` notation
-/
