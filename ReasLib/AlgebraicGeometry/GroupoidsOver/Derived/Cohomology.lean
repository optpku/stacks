module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.QuasiCoherent
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.TopCohomology

/-!
# Cohomology of quasi-coherent derived objects

The highest potentially nonzero cohomology sheaf of a quasi-coherent derived
object on the chaotic affine site is quasi-coherent.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.ModulesOnCategory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

namespace QC

/-- The degree-`i` cohomology sheaf of a quasi-coherent derived object on the
chaotic affine site. -/
abbrev cohomology (M : QC X) (i : ℤ) :
    SheafOfModules.{u + 1}
      (ringSheaf.{u + 1, u, u + 1} (⊥ : GrothendieckTopology (affineSite X))
        (affineStructureSheaf X)) :=
  (@DerivedCategory.homologyFunctor
      (SheafOfModules.{u + 1}
        (ringSheaf.{u + 1, u, u + 1} (⊥ : GrothendieckTopology (affineSite X))
          (affineStructureSheaf X)))
      inferInstance inferInstance
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
        (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X)))
      i).obj M.obj

end QC

/-- If a quasi-coherent derived object has vanishing cohomology above `b`, its
degree-`b` cohomology sheaf on the chaotic affine site is quasi-coherent. -/
theorem cohomology_isQuasicoherent (M : QC X) (b : ℤ)
    (hvanish : ∀ i : ℤ, b < i → IsZero (QC.cohomology M i)) :
    (QC.cohomology M b).IsQuasicoherent :=
  CategoryTheory.ModulesOnCategory.topCohomology_isQuasicoherent
    (affineStructureSheaf X) M b hvanish

end AlgebraicGeometry.GroupoidsOver
