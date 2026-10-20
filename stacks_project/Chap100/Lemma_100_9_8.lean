module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap100.Lemma_100_9_8_QuotientMap
public import stacks_project.Chap100.Lemma_100_9_8_Restrict
public import stacks_project.Chap94.Theorem_94_17_3
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Immersion
import StacksCheckRecall

/-!
# Immersions of restricted quotient stacks

An invariant locally closed subspace of the object space of a smooth groupoid in
algebraic spaces induces an immersion of the associated quotient stacks. Open and
closed invariant subspaces yield open and closed immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/- Lemma 100.9.8 (1): let `G` be a smooth groupoid in algebraic spaces with associated
algebraic stack `[U / R]`. If `Z ⊂ U` is an `R`-invariant locally closed subspace, then
`[Z / R_Z] ⟶ [U / R]` is an immersion of algebraic stacks, where `R_Z` is the restriction
of `R` to `Z`. -/
@[stacks 04YN]
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictQuotientHom_immersion : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (Z : LocallyClosedSubspace G.U.left)
    (hZ : G.IsLocallyClosedInvariant Z) ,
    Immersion (restrictQuotientHom G Z))

/- Lemma 100.9.8 (2): if in addition `Z ⊂ U` is open, then `[Z / R_Z] ⟶ [U / R]` is an
open immersion of algebraic stacks. -/
@[stacks 04YN]
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictQuotientHom_openImmersion : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (W : OpenSubspace G.U.left)
    (hW : G.IsOpenInvariant W) ,
    OpenImmersion (restrictQuotientHom G W.toLocallyClosed))

/- Lemma 100.9.8 (3): if in addition `Z ⊂ U` is closed, then `[Z / R_Z] ⟶ [U / R]` is a
closed immersion of algebraic stacks. -/
@[stacks 04YN]
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictQuotientHom_closedImmersion : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (C : ClosedSubspace G.U.left)
    (hC : G.IsLocallyClosedInvariant C.toLocallyClosed) ,
    ClosedImmersion (restrictQuotientHom G C.toLocallyClosed))

end AlgebraicGeometry.GroupoidAlgebraicSpace
