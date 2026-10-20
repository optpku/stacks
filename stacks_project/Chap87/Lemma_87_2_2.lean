module

public import ReasLib.AlgebraicGeometry.FormalScheme.Sheaf
import StacksCheckRecall

/-!
# Lemma 87.2.2

The functor of points of a formal scheme is a sheaf for the fpqc topology.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 87.2.2. The functor of points of a formal scheme satisfies the sheaf
condition for fpqc coverings on a small bound-closed category of test schemes. -/
@[stacks 0AI2] #check (AlgebraicGeometry.FormalScheme.functorOfPoints_isSheaf_fpqc :
  ∀ {P : ObjectProperty Scheme.{u}} (hP : Scheme.IsSmallBoundClosed P)
    (X : FormalScheme.{u}),
    Presheaf.IsSheaf (P.ι.restrictedTopology Scheme.fpqcTopology)
      ((AlgebraicGeometry.FormalScheme.functorOfPoints P).obj X))

#check (AlgebraicGeometry.FormalScheme.isSheaf_fpqc :
  ∀ (X : FormalScheme.{u}),
    Presheaf.IsSheaf Scheme.fpqcTopology
      (Scheme.toFormalScheme.op ⋙ yoneda.obj X))

#check (AlgebraicGeometry.FormalScheme.isSheaf_fppf :
  ∀ (X : FormalScheme.{u}),
    Presheaf.IsSheaf Scheme.fppfTopology
      (Scheme.toFormalScheme.op ⋙ yoneda.obj X))
