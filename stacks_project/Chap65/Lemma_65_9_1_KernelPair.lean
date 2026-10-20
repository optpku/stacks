module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPair

/-! Compatibility access to the reusable kernel-pair API. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Compatibility check for the reusable represented kernel-pair construction. -/
#check (kernelPair : {S : Scheme.{u}} → {F : AlgebraicSpace S} → {U : Over S} →
  (f : yoneda.obj U ⟶ F.functorOfPoints) → yoneda.relativelyRepresentable f → Scheme.PreRelation U)

end AlgebraicGeometry.AlgebraicSpace
