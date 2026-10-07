module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Functor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.FiniteProjective
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.FinitePresentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Morphism
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Presheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Local
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Monoidal
import StacksCheckRecall

/-!
# Associated module sheaves

This is the stable import surface for modules over global scalars and their associated module
sheaves. The leaf files separate the functor, adjunction, base-change and morphism comparison,
finite-projective restriction, quasi-coherent lift, tensor-presheaf model, free presentations,
stalks, and local properties.
-/

@[expose] public section

/- Stacks 01BH: associated module functor. -/
@[stacks 01BH "associated module functor"] #check AlgebraicGeometry.RingedSpace.Module.Associated.functor

/- Stacks 01BI: associated module sheaf. -/
@[stacks 01BI "associated module sheaf"] #check AlgebraicGeometry.RingedSpace.Module.Associated.obj

/- The geometric-sections model is a reusable implementation layer for the adjunction; the
   source-facing owner is `adjunction` below. -/

/- Stacks 01BH: associated-module adjunction. -/
@[stacks 01BH "associated-module adjunction"] #check AlgebraicGeometry.RingedSpace.Module.Associated.adjunction

/- Stacks 01BJ: associated-module base change. -/
@[stacks 01BJ "associated-module base change"] #check AlgebraicGeometry.RingedSpace.Module.Associated.BaseChange.functor

/- Stacks 01BH: quasi-coherent associated-module lift. -/
@[stacks 01BH "quasi-coherent associated-module lift"] #check AlgebraicGeometry.RingedSpace.Module.Associated.qcFunctor

/- Stacks 01BH: tensor-presheaf comparison (tagged on the leaf owner). -/

@[stacks 01BH "free-presentation comparison"] #check AlgebraicGeometry.RingedSpace.Module.Associated.Presentation.iso

/- Stacks 01BH: associated-sheaf stalk comparison. -/
@[stacks 01BH "associated-sheaf stalk comparison"] #check AlgebraicGeometry.RingedSpace.Module.Associated.stalkComparison

@[stacks 01BK "quasi-coherent modules are locally associated"] #check AlgebraicGeometry.RingedSpace.Module.Associated.IsLocallyAssociated.ofIsQuasicoherent
