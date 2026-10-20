module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction.LocallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallFunctoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Algebraic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The morphism `[Z / R_Z] ⟶ [U / R]` of quotient stacks induced by restriction to a
locally closed subspace. -/
def restrictQuotientHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) :
    SmallQuotient.quotientStack (restrict G Z) ⟶ SmallQuotient.quotientStack G :=
  Hom.quotientStackHom (restrictHom G Z)

/-- `restrictQuotientHom` is `quotientStackHom` of `restrictHom`. -/
theorem restrictQuotientHom_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) :
    restrictQuotientHom G Z = Hom.quotientStackHom (restrictHom G Z) :=
  rfl

/-- The quotient stack of the restriction of a smooth groupoid to an invariant locally closed
subspace is an algebraic stack. -/
theorem algebraicStack_restrictQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (Z : LocallyClosedSubspace G.U.left)
    (hZ : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι) :
    AlgebraicStack (SmallQuotient.quotientStack (restrict G Z)) :=
  @instAlgebraicStack_quotientStack S B (restrict G Z) (smooth_restrict G Z hZ)

/-- The quotient stack of the restriction of a smooth groupoid to an invariant open subspace
is an algebraic stack. -/
theorem algebraicStack_restrictQuotient_open {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (W : OpenSubspace G.U.left)
    (hW : CategoryTheory.Morphism.IsForwardInvariant G.s.left G.t.left W.ι) :
    AlgebraicStack (SmallQuotient.quotientStack (restrict G W.toLocallyClosed)) :=
  @instAlgebraicStack_quotientStack S B (restrict G W.toLocallyClosed)
    (smooth_restrict_open G W hW)

/-- The quotient morphism induced by an invariant locally closed subspace of a smooth
groupoid is an immersion. -/
theorem restrictQuotientHom_immersion {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (Z : LocallyClosedSubspace G.U.left)
    (hZ : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left Z.ι) :
    Immersion (restrictQuotientHom G Z) :=
  sorry

/-- The quotient morphism induced by an invariant open subspace of a smooth groupoid
is an open immersion. -/
theorem restrictQuotientHom_openImmersion {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (W : OpenSubspace G.U.left)
    (hW : CategoryTheory.Morphism.IsForwardInvariant G.s.left G.t.left W.ι) :
    OpenImmersion (restrictQuotientHom G W.toLocallyClosed) :=
  sorry

/-- The quotient morphism induced by an invariant closed subspace of a smooth groupoid
is a closed immersion. -/
theorem restrictQuotientHom_closedImmersion {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (C : ClosedSubspace G.U.left)
    (hC : CategoryTheory.Morphism.IsPullbackInvariant G.s.left G.t.left C.toLocallyClosed.ι) :
    ClosedImmersion (restrictQuotientHom G C.toLocallyClosed) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
