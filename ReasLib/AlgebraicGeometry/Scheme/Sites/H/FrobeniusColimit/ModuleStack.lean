module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.TwoGenerator.FrobeniusColimit
public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.FrobeniusColimit.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.GroupoidDescent
public import ReasLib.AlgebraicGeometry.Scheme.Spec.AlmostBlowup.FrobeniusColimit

/-!
# The stack of finite locally free Frobenius-colimit modules

Finite locally free modules over Frobenius-colimit structure sheaves form a stack in groupoids
for the h topology.  Over a quasi-compact and quasi-separated object, its fibre is equivalent
to the Frobenius colimit of vector bundles.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit

/-- Finite locally free modules over Frobenius-colimit structure sheaves form a stack in
groupoids for the chosen big h topology. -/
@[instance]
theorem moduleFiberedCategoryIsStack (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    IsStack.InGroupoids (bigTopology Schh S) (moduleFiberedCategory p Schh S).p := sorry

/-- Over a quasi-compact and quasi-separated represented scheme, the fibre of the
Frobenius-colimit module stack is equivalent to the core of the Frobenius colimit of vector
bundles. -/
theorem moduleFiberEquivVectorBundleColimit (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S)
    [CompactSpace ((ChosenBigSite.sliceToScheme Schh S).obj U)]
    [QuasiSeparatedSpace ((ChosenBigSite.sliceToScheme Schh S).obj U)] :
    -- Local instance justification (search instability): derive the represented scheme's characteristic only in this conclusion.
    letI : Scheme.IsCharP ((ChosenBigSite.sliceToScheme Schh S).obj U) p :=
      Scheme.Hom.isCharP_of_target (Schh.toScheme.map U.hom)
    Nonempty ((moduleFiberedCategory p Schh S).p.Fiber U ≌
      Core (Scheme.FrobeniusColimit.vectorBundleColimit p
        ((ChosenBigSite.sliceToScheme Schh S).obj U))) := sorry

end AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit
