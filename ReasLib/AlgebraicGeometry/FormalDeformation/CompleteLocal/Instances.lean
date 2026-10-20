module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal

/-!
# Stored structures on complete local algebras

This opt-in leaf makes the structures already carried by a complete local algebra
available to typeclass inference, without changing the carrier or algebra map.
-/

@[expose] public section

attribute [instance] CompleteLocalAlgCat.algebra CompleteLocalAlgCat.isLocalRing
  CompleteLocalAlgCat.isNoetherianRing CompleteLocalAlgCat.isCompleteLocalRing
  CompleteLocalAlgCat.Hom.isLocalHom
