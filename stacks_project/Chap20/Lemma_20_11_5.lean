module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.SpectralSequence
import StacksCheckRecall

@[expose] public section

/- Lemma 20.11.5 (01ES): an indexed open cover and a module sheaf determine a bounded convergent
Cech-to-cohomology spectral-sequence system with explicit page-two and abutment identifications. -/
@[stacks 01ES]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.spectralSequenceSystem_nonempty_of_iSup_eq

#check @AlgebraicGeometry.RingedSpace.ModuleCech.SpectralSequenceSystem
#check @AlgebraicGeometry.RingedSpace.ModuleCech.spectralSequenceSystem_nonempty
