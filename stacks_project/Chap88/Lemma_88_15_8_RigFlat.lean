module

public import ReasLib.RingTheory.AdicCompletion.RigFlat

/-!
# Rig-flat homomorphisms of adic Noetherian rings

This module preserves the chapter-facing names for the reusable rig-flat API.
-/

@[expose] public section

/- The ring-homomorphism topological finite-type predicate. -/
#check RingHom.TopologicallyFiniteType

/- A constructor for the ring-homomorphism topological finite-type predicate. -/
#check RingHom.TopologicallyFiniteType.of_algebra

/- The specification of the ring-homomorphism topological finite-type predicate. -/
#check RingHom.TopologicallyFiniteType.iff

/- The algebra-level naive rig-flatness predicate. -/
#check Algebra.NaiveRigFlat

/- The identity instance for algebra-level naive rig-flatness. -/
#check Algebra.NaiveRigFlat.id

/- The specification of algebra-level naive rig-flatness. -/
#check Algebra.NaiveRigFlat.iff

/- The inferred specification of algebra-level naive rig-flatness. -/
#check Algebra.NaiveRigFlat.spec

/- The localization-flatness consequence of algebra-level naive rig-flatness. -/
#check Algebra.NaiveRigFlat.flat_away

/- The ring-homomorphism-level naive rig-flatness predicate. -/
#check RingHom.NaiveRigFlat

/- The identity instance for ring-homomorphism-level naive rig-flatness. -/
#check RingHom.NaiveRigFlat.id

/- The specification of ring-homomorphism-level naive rig-flatness. -/
#check RingHom.NaiveRigFlat.iff

/- The inferred specification of ring-homomorphism-level naive rig-flatness. -/
#check RingHom.NaiveRigFlat.spec

/- Adic continuity of the principal-localization map. -/
#check completedPrincipalLocalization.awayMap_adicContinuous

/- The map induced on completed principal localizations. -/
#check completedPrincipalLocalization.map

/- The completion-map characterization of the induced map. -/
#check completedPrincipalLocalization.map_eq

/- The principal-localization extension property of the induced map. -/
#check completedPrincipalLocalization.map_comp_away

/- The base-ring extension property of the induced map. -/
#check completedPrincipalLocalization.map_comp

/- The ring-homomorphism-level rig-flatness predicate. -/
#check RingHom.RigFlat

/- The identity instance for ring-homomorphism-level rig-flatness. -/
#check RingHom.RigFlat.id

/- The specification of ring-homomorphism-level rig-flatness. -/
#check RingHom.RigFlat.iff

/- The inferred specification of ring-homomorphism-level rig-flatness. -/
#check RingHom.RigFlat.spec

/- The naive rig-flatness consequence of rig-flatness. -/
#check RingHom.RigFlat.toNaive

/- Rig-flatness descent along a faithfully flat square. -/
#check RingHom.RigFlat.of_faithfullyFlat_square
