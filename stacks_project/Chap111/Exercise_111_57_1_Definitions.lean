module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.LocalRing.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Modules.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

variable {X Y : Scheme.{u}} (x : X) (F : X.Modules) (U : X.Opens) (f : X ⟶ Y)

/- Exercise 111.57.1 (Definitions) (1): the local ring of `X` at a point `x`. -/
@[stacks 0AAM] #check (AlgebraicGeometry.Scheme.localRing X x : CommRingCat)

#check (inferInstance : IsLocalRing (X.presheaf.stalk x))

/- Exercise 111.57.1 (Definitions) (2): a quasi-coherent sheaf of `𝒪_X`-modules. -/
@[stacks 0AAM] #check (AlgebraicGeometry.Scheme.Modules.IsQuasicoherent F : Prop)

section
variable [IsLocallyNoetherian X] (ℱ : X.Modules)

/- Exercise 111.57.1 (Definitions) (3): a coherent sheaf of `𝒪_X`-modules,
assuming `X` is locally Noetherian. -/
@[stacks 0AAM] #check (SheafOfModules.IsCoherent ℱ : Prop)

end

/- Exercise 111.57.1 (Definitions) (4): an affine open of `X`. -/
@[stacks 0AAM] #check (AlgebraicGeometry.Scheme.IsAffineOpen U : Prop)

/- Exercise 111.57.1 (Definitions) (5): a finite morphism of schemes `X ⟶ Y`. -/
@[stacks 0AAM] #check (AlgebraicGeometry.Scheme.IsFinite f : Prop)

#check (AlgebraicGeometry.isFinite_iff f :
  AlgebraicGeometry.IsFinite f ↔
    IsAffineHom f ∧
      ∀ U : Y.Opens, AlgebraicGeometry.IsAffineOpen U → (f.app U).hom.Finite)
