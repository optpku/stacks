module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Ordered
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealComplement

@[expose] public section

open AlgebraicGeometry CategoryTheory
open LocalizedModule.Away.Cech

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace IdealComplement

variable {A : Type u} [CommRing A]

/-- The ordered localization Čech complex computes cohomology on an affine ideal complement. -/
theorem orderedCechHomology_iso {t : ℕ} (f : Fin t → A) (M : ModuleCat A) (n : ℕ) :
    IsIsomorphic ((Ordered.complex f M).homology n)
      (cohomology (Ideal.span (Set.range f))
        ((tilde M).restrict (idealComplementOpens (Ideal.span (Set.range f))).ι) n) := sorry

end IdealComplement
end AlgebraicGeometry.Scheme.Modules
