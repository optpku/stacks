/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
public import stacks_project.Chap67.Lemma_67_20_7_AffineOver

/-!
# Affine relative spectrum of a quasi-coherent algebra

This file records that the structure morphism of the relative spectrum of a
quasi-coherent algebra on an algebraic space is affine, and packages it as an
object of `AffineMorphismOver`. Correspondence with the algebra is stated using
the in-scope structure-sheaf map `commRingStructureSheafMap`, not a clone of
the Lemma 67.20.7 pushforward API (that file cannot be imported alongside
`relativeSpecπ`, because both export `commRingPushforward`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure morphism of the relative spectrum of a quasi-coherent `𝒪_X`-algebra
is affine. -/
instance instAffine_relativeSpecπ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) : Affine (relativeSpecπ A) :=
  sorry

namespace AffineMorphismOver

/-- The algebraic space affine over `X` corresponding to a quasi-coherent
`𝒪_X`-algebra, with structure morphism `relativeSpecπ A`. -/
def ofQcAlgebra {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) : AffineMorphismOver X where
  obj := Over.mk (relativeSpecπ A)
  property := instAffine_relativeSpecπ A

/-- The slice object of `ofQcAlgebra A` is the over-object of `relativeSpecπ A`. -/
theorem ofQcAlgebra_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    (ofQcAlgebra A).obj = Over.mk (relativeSpecπ A) :=
  sorry

/-- The structure morphism of `ofQcAlgebra A` is `relativeSpecπ A`. -/
theorem ofQcAlgebra_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    (ofQcAlgebra A).obj.hom = relativeSpecπ A :=
  sorry

/-- The underlying algebraic space of `ofQcAlgebra A` is `relativeSpec A`. -/
theorem ofQcAlgebra_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    (ofQcAlgebra A).obj.left = relativeSpec A :=
  sorry

/-- The quasi-coherent `𝒪_X`-algebra obtained from an algebraic space affine over
`X` by the in-scope structure-sheaf map `commRingStructureSheafMap`. -/
def commRingStructureQcAlgebra {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : AffineMorphismOver X) : X.QcAlgebraUnder where
  obj := Under.mk (commRingStructureSheafMap Y.obj.hom)
  property := sorry

/-- The underlying algebra of `commRingStructureQcAlgebra Y` is the raw
structure-sheaf map of `Y`. -/
theorem commRingStructureQcAlgebra_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : AffineMorphismOver X) :
    (commRingStructureQcAlgebra Y).obj =
      Under.mk (commRingStructureSheafMap Y.obj.hom) :=
  sorry

/-- The structure-sheaf algebra of `ofQcAlgebra A` is isomorphic to `A`. -/
theorem commRingStructureQcAlgebra_ofQcAlgebra {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    Nonempty (commRingStructureQcAlgebra (ofQcAlgebra A) ≅ A) :=
  sorry

/-- Any algebraic space affine over `X` whose structure-sheaf algebra is isomorphic
to `A` is isomorphic to `ofQcAlgebra A`. -/
theorem ofQcAlgebra_of_commRingStructureQcAlgebra {S : Scheme.{u}}
    {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) (Y : AffineMorphismOver X)
    (h_iso : Nonempty (commRingStructureQcAlgebra Y ≅ A)) :
    Nonempty (Y ≅ ofQcAlgebra A) :=
  sorry

end AffineMorphismOver

end AlgebraicGeometry.AlgebraicSpace
