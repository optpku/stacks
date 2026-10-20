module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.SingularPointSequence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Dualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.RingTheory.Normal.RationalSingularity

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace IsRationalSingularity

/-- A two-dimensional rational singularity with a dualizing complex admits a finite
sequence of singular-point blowups through normal schemes with invertible terminal
dualizing module. -/
theorem existsSingularPointBlowupSequence
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    (h_dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing) :
    ∃ (X : Scheme.{u})
      (s : Scheme.SingularPointBlowupSequence (Spec (.of A)) X)
      (hX : IsLocallyNoetherian X) (ωX : X.Modules),
      s.EveryTarget (fun Y ↦ Y.isNormal) ∧
        @Scheme.IsDualizingModule X hX ωX ∧ Scheme.Modules.Invertible ωX := sorry

end IsRationalSingularity
