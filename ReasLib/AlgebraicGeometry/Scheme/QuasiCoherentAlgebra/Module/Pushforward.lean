module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Module
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Pushforward
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Pushforward as a module over the pushed-forward structure sheaf

This file defines direct image with its natural module structure over the direct
image of the structure sheaf and restricts it to quasi-coherent modules.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

namespace Modules

/-- Direct image of module sheaves, retaining the natural module structure over
the pushed-forward structure sheaf. -/
noncomputable def pushforwardAsModule (f : X ⟶ S) :
    X.Modules ⥤
      ringedSiteModuleCategory (Opens.grothendieckTopology S)
        ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf) :=
  SheafOfModules.pushforward
    (𝟙 (ringSheaf (Opens.grothendieckTopology S)
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf)))

end Modules

namespace QCoh

namespace pushforwardAsModule

/-- Direct image as a module over the pushed-forward structure sheaf carries
quasi-coherent modules to quasi-coherent modules along a quasi-compact,
quasi-separated morphism. -/
theorem mapsTo (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    quasiCoherentModuleProperty X ≤
      (pushforwardStructureSheafQcAlgebra f).quasiCoherentModuleProperty.inverseImage
        (Modules.pushforwardAsModule f) := sorry

end pushforwardAsModule

/-- Direct image from quasi-coherent modules to quasi-coherent modules over the
pushed-forward structure sheaf. -/
noncomputable def pushforwardAsModule
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    QCoh X ⥤ (pushforwardStructureSheafQcAlgebra f).QCoh :=
  FullSubcategory.restrict
    (Modules.pushforwardAsModule f) (pushforwardAsModule.mapsTo f)

namespace pushforwardAsModule

/-- Forgetting quasi-coherence after direct image as a module over the
pushed-forward structure sheaf recovers the ambient direct-image functor. -/
noncomputable def inclusionIso
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    QCoh.pushforwardAsModule f ⋙
        QcAlgebraUnder.QCoh.inclusion (pushforwardStructureSheafQcAlgebra f) ≅
      QCoh.inclusion X ⋙ Modules.pushforwardAsModule f :=
  FullSubcategory.restrict.compιIso
    (Modules.pushforwardAsModule f) (mapsTo f)

/-- For an affine morphism, direct image is an equivalence from quasi-coherent
modules to quasi-coherent modules over the pushed-forward structure sheaf. -/
instance isEquivalence (f : X ⟶ S) [IsAffineHom f] :
    Functor.IsEquivalence (QCoh.pushforwardAsModule f) := sorry

end pushforwardAsModule

end QCoh

end AlgebraicGeometry.Scheme
