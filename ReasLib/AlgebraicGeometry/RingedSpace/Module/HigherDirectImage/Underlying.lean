module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
public import ReasLib.Topology.Sheaf.HigherDirectImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying additive sheaves of higher direct images

For a morphism of ringed spaces, forgetting module structure commutes with higher direct image.
The primary interface is functorial; the objectwise theorem is its convenient projection for
ordinary module sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.Underlying

variable {X Y : RingedSpace.{u}}
variable [HasInjectiveResolutions
  (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- Higher direct image followed by the underlying-additive-sheaf functor is naturally
isomorphic to higher direct image of the underlying additive sheaf. -/
@[stacks 01F1 "functorial underlying higher direct-image comparison"]
theorem functor_isIsomorphic (f : X ⟶ Y)
    (i : ℕ) :
    IsIsomorphic
      (higherDirectImageModuleFunctor f i ⋙ moduleUnderlyingSheaf Y)
      (moduleUnderlyingSheaf X ⋙
        TopCat.Sheaf.higherDirectImageFunctor f.hom.base i) := sorry

/-- The underlying additive sheaf of a higher direct image is isomorphic to the higher direct
image of the underlying additive sheaf. -/
@[stacks 01F1 "underlying higher direct-image comparison"]
theorem obj_isIsomorphic (f : X ⟶ Y)
    (F : X.Modules) (i : ℕ) :
    IsIsomorphic
      ((moduleUnderlyingSheaf Y).obj (higherDirectImageModule f F i))
      (TopCat.Sheaf.higherDirectImage f.hom.base ((moduleUnderlyingSheaf X).obj F) i) := sorry

end AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.Underlying
