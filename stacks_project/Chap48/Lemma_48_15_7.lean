module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 48.15.7 -/
@[stacks 0BRT]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.differentialExteriorShift_isomorphic_relativeDualizingComplex :
    ∀ {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) (d : ℕ),
      [SmoothOfRelativeDimension d f] → [IsProper f] →
      ∀ (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh X)
        (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a),
        IsIsomorphic (Scheme.Hom.differentialExteriorShift f d)
          (Scheme.DerivedQCoh.relativeDualizingComplex f a aAdjunction))
