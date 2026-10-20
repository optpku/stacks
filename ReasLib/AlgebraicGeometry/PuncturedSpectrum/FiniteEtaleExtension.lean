module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.PrincipalQuotient
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.RingTheory.Depth
public import Mathlib.Algebra.Homology.LocalCohomology

@[expose] public section

open CategoryTheory
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- A finite étale cover of the punctured spectrum extends across the closed
point when its principal-quotient restriction extends and the first two local
cohomology modules are annihilated by powers of the defining element. -/
theorem finiteEtale_extends_of_localCohomology_annihilation
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : maximalIdeal A)
    (hH1 : Module.IsAnnihilatedByPower (Ideal.span ({(f : A)} : Set A))
      ((localCohomology (maximalIdeal A) 1).obj (ModuleCat.of A A)))
    (hH2 : Module.IsAnnihilatedByPower (Ideal.span ({(f : A)} : Set A))
      ((localCohomology (maximalIdeal A) 2).obj (ModuleCat.of A A)))
    (V : Scheme.FiniteEtale (scheme A))
    (Y0 : Scheme.FiniteEtale (Spec (CommRingCat.of (A ⧸ principalIdeal (f : A)))))
    (hV0 : Nonempty
      ((Scheme.finiteEtaleBaseChange (principalQuotientMap f)).obj V ≅
        (Scheme.finiteEtaleBaseChange
          (puncturedOpen (A ⧸ principalIdeal (f : A))).ι).obj Y0)) :
    ∃ Y : Scheme.FiniteEtale (Spec (CommRingCat.of A)),
      Nonempty ((Scheme.finiteEtaleBaseChange (puncturedOpen A).ι).obj Y ≅ V) := sorry

/-- A finite étale cover of the punctured spectrum extends across the closed
point when the local ring has depth at least three and its principal-quotient
restriction extends across the quotient's closed point. -/
theorem finiteEtale_extends_of_depth_ge_three
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : maximalIdeal A)
    (hdepth : (3 : ℕ∞) ≤ moduleDepth A A)
    (V : Scheme.FiniteEtale (scheme A))
    (Y0 : Scheme.FiniteEtale (Spec (CommRingCat.of (A ⧸ principalIdeal (f : A)))))
    (hV0 : Nonempty
      ((Scheme.finiteEtaleBaseChange (principalQuotientMap f)).obj V ≅
        (Scheme.finiteEtaleBaseChange
          (puncturedOpen (A ⧸ principalIdeal (f : A))).ι).obj Y0)) :
    ∃ Y : Scheme.FiniteEtale (Spec (CommRingCat.of A)),
      Nonempty ((Scheme.finiteEtaleBaseChange (puncturedOpen A).ι).obj Y ≅ V) := sorry

end AlgebraicGeometry.PuncturedSpectrum
