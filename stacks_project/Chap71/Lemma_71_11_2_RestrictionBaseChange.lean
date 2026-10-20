module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.BaseChange
public import stacks_project.Chap71.Lemma_71_11_2_RestrictionMonoidal

/-! The represented-scheme direct-image square has its public owner; the extension mate
continues to use the source extension adjunction. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
variable {S : Scheme.{u}} {T Z : Over S}

/-- Inverse images commute with extension, by uniqueness of their actual adjunctions. -/
def extensionPullbackIso (t : T ⟶ Z) :
    Scheme.Modules.pullback t.left ⋙ extension T ≅
      extension Z ⋙ Modules.pullback (ofOverMap t) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction t.left).comp
      (extensionAdjunction T)).leftAdjointUniq
    (((extensionAdjunction Z).comp
      (Modules.pullbackPushforwardAdjunction (ofOverMap t))).ofNatIsoRight
        (pushforwardComparisonIso t))


end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
