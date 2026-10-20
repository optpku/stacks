/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Locality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Over

/-!
# Relative spectra as affine objects over an algebraic space

The relative spectrum of a quasi-coherent algebra has an affine structural
projection and defines an object of the category of affine morphisms over its base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure morphism of the relative spectrum of a quasi-coherent algebra is affine. -/
instance instAffine_relativeSpecπ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) : Affine (relativeSpecπ A) :=
  (Affine.iff_representableAffine (relativeSpecπ A)).2
    ⟨relativeSpecπ_relativelyRepresentable A, relativeSpecπ_presheaf_affine A⟩

namespace AffineMorphismOver

/-- The relative spectrum of a quasi-coherent algebra as an affine object over its base. -/
def ofQcAlgebra {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) : AffineMorphismOver X where
  obj := Over.mk (relativeSpecπ A)
  property := instAffine_relativeSpecπ A

/-- The slice object of the affine relative spectrum is the over-object of its projection. -/
theorem ofQcAlgebra_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    (ofQcAlgebra A).obj = Over.mk (relativeSpecπ A) :=
  rfl

/-- The structure morphism of the affine relative spectrum is its canonical projection. -/
theorem ofQcAlgebra_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    (ofQcAlgebra A).obj.hom = relativeSpecπ A :=
  rfl

/-- The underlying algebraic space of the affine relative spectrum is the relative spectrum. -/
theorem ofQcAlgebra_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    (ofQcAlgebra A).obj.left = relativeSpec A :=
  rfl

/-- An affine object whose direct-image structure algebra is isomorphic to a
quasi-coherent algebra is isomorphic over the base to its relative spectrum. -/
theorem ofQcAlgebra_unique {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (Y : AffineMorphismOver X)
    (h_iso : Nonempty (Under.mk (commStructureSheafMap Y.obj.hom) ≅ A.obj)) :
    Nonempty (Y ≅ ofQcAlgebra A) :=
  sorry

end AffineMorphismOver

end AlgebraicGeometry.AlgebraicSpace
