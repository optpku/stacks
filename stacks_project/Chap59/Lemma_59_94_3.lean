module

public import stacks_project.Chap59.Lemma_59_94_2
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.VanishingCycles.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.EtaleVanishingCycles

universe u

/- Lemma 59.94.3 (1): specialization on geometric stalks of the derived direct image
is invertible for a proper morphism locally acyclic relative to bounded-below étale
coefficients with torsion cohomology. -/
@[stacks 0GJW] #check (AlgebraicGeometry.Scheme.Etale.isIso_derivedPushforward_specializationMap :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (K : DerivedCategory.Plus (Coefficients X)) [LocallyAcyclicRelative f K.obj]
    (hTorsion : DerivedCategory.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Coefficients X)) K.obj),
    IsIso (Etale.derivedPushforward_specializationMap f s t point point_over K.obj))

/- Lemma 59.94.3 (2): cospecialization from geometric-fibre cohomology at `t` to that
at `s` is invertible for a proper morphism locally acyclic relative to bounded-below
étale coefficients with torsion cohomology. -/
@[stacks 0GJW] #check (AlgebraicGeometry.Scheme.Etale.Cohomology.isIso_cospecialization :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (K : DerivedCategory.Plus (Coefficients X)) [LocallyAcyclicRelative f K.obj]
    (hTorsion : DerivedCategory.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Coefficients X)) K.obj),
    IsIso (Etale.Cohomology.cospecialization f s t point point_over K))
