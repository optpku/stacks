module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.PuncturedSpectrum
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 58.29.2: in the situation of Lemma 58.29.1, vanishing of the
structure-sheaf cohomology in all degrees at least `ringKrullDim A - 1` implies
that `V` is affine. -/
@[stacks 0ECC] #check (AlgebraicGeometry.Scheme.Hom.isAffine_of_cohomology_isZero :
  ∀
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [IsRegularLocalRing A]
    {V : Scheme.{u}} (f : V ⟶ Spec (CommRingCat.of A)) [Etale f] [QuasiCompact f]
    (h_m : IsLocalRing.closedPoint A ∉ Set.range f)
    (g : V ⟶ PuncturedSpectrum.scheme A) [IsAffineHom g]
    (h_factor : g ≫ (PuncturedSpectrum.puncturedOpen A).ι = f)
    (h_vanish : ∀ i : ℕ, (ringKrullDim A).unbotD 0 - 1 ≤ (i : ℕ∞) →
      IsZero (Scheme.Hom.cohomology f
        (SheafOfModules.unit V.ringCatSheaf : V.Modules) i)),
    IsAffine V)
