module

public import ReasLib.Topology.Sheaf.Cohomology.CompactOpen.Specializing
import StacksCheckRecall

@[expose] public section

/- Lemma 20.22.1 (1) (0A3D): in a spectral space, the canonical map from the colimit of
cohomology over compact-open neighbourhoods of a compact subset `E` to cohomology on
`nhdsKer E` is an isomorphism. -/
@[stacks 0A3D "(1)"]
#check @TopCat.Sheaf.Cohomology.CompactOpen.Specializing.comparison_isIso_of_isCompact

/- Lemma 20.22.1 (2) (0A3D): for a constructible subset `E`, the canonical map from the
colimit of the groups on `U \ E` to cohomology on `nhdsKer E \ E` is an isomorphism. -/
@[stacks 0A3D "(2)"]
#check @TopCat.Sheaf.Cohomology.CompactOpen.Specializing.Sdiff.comparison_isIso_of_isConstructible

#check @TopCat.Sheaf.Cohomology.CompactOpen.Specializing.diagram
#check @TopCat.Sheaf.Cohomology.CompactOpen.Specializing.comparison
#check @TopCat.Sheaf.Cohomology.CompactOpen.Specializing.Sdiff.diagram
#check @TopCat.Sheaf.Cohomology.CompactOpen.Specializing.Sdiff.comparison
