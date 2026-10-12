/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Grassmannian.Model
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Datum

/-!
# Rank-one Grassmannian quotients and projective space

Rank-one quotients of a free module sheaf correspond naturally to invertible module sheaves
equipped with a generating family of sections.  This identifies the Grassmannian functor in
successive dimensions with the projective-space datum functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Grassmannian.Quotient

/-- A quotient of a free module of rank `n + 1` with Grassmannian index `n` has an invertible
target module. -/
theorem selfSucc_isInvertible (n : ℕ) {S : Scheme.{u}}
    (Q : Grassmannian.Quotient n (n + 1) S) :
    Scheme.Modules.Invertible Q.module := sorry

/-- The sections induced by a rank-one Grassmannian quotient generate its target module. -/
theorem selfSucc_sectionFamilyHom_epi (n : ℕ) {S : Scheme.{u}}
    (Q : Grassmannian.Quotient n (n + 1) S) :
    Epi (ProjectiveSpaceDatum.sectionFamilyHom Q.module n
      (fun i ↦ Q.module.freeHomEquiv Q.map (ULift.up i))) := sorry

/-- A rank-one Grassmannian quotient determines an invertible module with `n + 1` generating
sections. -/
def toProjectiveSpaceDatum (n : ℕ) {S : Scheme.{u}}
    (Q : Grassmannian.Quotient n (n + 1) S) : ProjectiveSpaceDatum n S where
  lineBundle := Q.module
  invertible_lineBundle := selfSucc_isInvertible n Q
  sections := fun i ↦ Q.module.freeHomEquiv Q.map (ULift.up i)
  generates := selfSucc_sectionFamilyHom_epi n Q

/-- Compatible isomorphisms of rank-one Grassmannian quotients induce equivalent
projective-space data. -/
theorem rel_toProjectiveSpaceDatum (n : ℕ) {S : Scheme.{u}}
    {Q Q' : Grassmannian.Quotient n (n + 1) S} :
    Rel Q Q' →
      ProjectiveSpaceDatum.Equivalent
        (toProjectiveSpaceDatum n Q) (toProjectiveSpaceDatum n Q') := sorry

/-- Conversion of a rank-one Grassmannian quotient to projective-space data commutes with
pullback up to the defining equivalence of projective-space data. -/
theorem toProjectiveSpaceDatum_pullback_equivalent (n : ℕ) {S T : Scheme.{u}}
    (f : T ⟶ S) (Q : Grassmannian.Quotient n (n + 1) S) :
    ProjectiveSpaceDatum.Equivalent
      (toProjectiveSpaceDatum n (pullback f Q))
      (ProjectiveSpaceDatum.pullback f (toProjectiveSpaceDatum n Q)) := sorry

end Grassmannian.Quotient

namespace ProjectiveSpaceDatum

/-- The line bundle of projective-space data has the rank required for a quotient of a free
module of rank `n + 1` with Grassmannian index `n`. -/
theorem isFiniteLocallyFreeOfRank_selfSucc (n : ℕ) {S : Scheme.{u}}
    (τ : ProjectiveSpaceDatum n S) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank ((n + 1) - n) τ.lineBundle := sorry

/-- An invertible module with `n + 1` generating sections determines a rank-one Grassmannian
quotient. -/
def toGrassmannianQuotient (n : ℕ) {S : Scheme.{u}}
    (τ : ProjectiveSpaceDatum n S) : Grassmannian.Quotient n (n + 1) S where
  module := τ.lineBundle
  isLocallyFree := isFiniteLocallyFreeOfRank_selfSucc n τ
  map := sectionFamilyHom τ.lineBundle n τ.sections
  map_epi := τ.generates

/-- Equivalent projective-space data determine related rank-one Grassmannian quotients. -/
theorem equivalent_toGrassmannianQuotient (n : ℕ) {S : Scheme.{u}}
    {τ τ' : ProjectiveSpaceDatum n S} :
    Equivalent τ τ' →
      Grassmannian.Quotient.Rel
        (toGrassmannianQuotient n τ) (toGrassmannianQuotient n τ') := sorry

end ProjectiveSpaceDatum

namespace Grassmannian.Quotient

/-- Passing from a rank-one Grassmannian quotient to projective-space data and back preserves
its Grassmannian quotient class. -/
theorem toProjectiveSpaceDatum_toGrassmannianQuotient_rel (n : ℕ) {S : Scheme.{u}}
    (Q : Grassmannian.Quotient n (n + 1) S) :
    Rel (ProjectiveSpaceDatum.toGrassmannianQuotient n
      (toProjectiveSpaceDatum n Q)) Q := sorry

end Grassmannian.Quotient

namespace ProjectiveSpaceDatum

/-- Passing from projective-space data to a rank-one Grassmannian quotient and back preserves
its projective-space datum class. -/
theorem toGrassmannianQuotient_toProjectiveSpaceDatum_equivalent
    (n : ℕ) {S : Scheme.{u}} (τ : ProjectiveSpaceDatum n S) :
    Equivalent
      (Grassmannian.Quotient.toProjectiveSpaceDatum n
        (toGrassmannianQuotient n τ)) τ := sorry

end ProjectiveSpaceDatum

namespace Grassmannian

/-- Send a rank-one Grassmannian quotient class to its projective-space datum class. -/
def toProjectiveSpaceDatumClass (n : ℕ) {S : Scheme.{u}} :
    (functor n (n + 1)).obj (Opposite.op S) → ProjectiveSpaceDatumClass n S :=
  _root_.Quotient.map (Quotient.toProjectiveSpaceDatum n)
    (fun {_ _} h ↦ Quotient.rel_toProjectiveSpaceDatum n h)

/-- Send a projective-space datum class to its rank-one Grassmannian quotient class. -/
def ofProjectiveSpaceDatumClass (n : ℕ) {S : Scheme.{u}} :
    ProjectiveSpaceDatumClass n S → (functor n (n + 1)).obj (Opposite.op S) :=
  _root_.Quotient.map (ProjectiveSpaceDatum.toGrassmannianQuotient n)
    (fun {_ _} h ↦ ProjectiveSpaceDatum.equivalent_toGrassmannianQuotient n h)

/-- Converting a Grassmannian class to a projective-space datum class and back is the identity.
-/
theorem ofProjectiveSpaceDatumClass_toProjectiveSpaceDatumClass
    (n : ℕ) {S : Scheme.{u}} (Q : (functor n (n + 1)).obj (Opposite.op S)) :
    ofProjectiveSpaceDatumClass n (toProjectiveSpaceDatumClass n Q) = Q := sorry

/-- Converting a projective-space datum class to a Grassmannian class and back is the identity.
-/
theorem toProjectiveSpaceDatumClass_ofProjectiveSpaceDatumClass
    (n : ℕ) {S : Scheme.{u}} (τ : ProjectiveSpaceDatumClass n S) :
    toProjectiveSpaceDatumClass n (ofProjectiveSpaceDatumClass n τ) = τ := sorry

/-- Rank-one Grassmannian quotient classes are equivalent to projective-space datum classes. -/
def selfSuccDatumClassEquiv (n : ℕ) (S : Scheme.{u}) :
    (functor n (n + 1)).obj (Opposite.op S) ≃ ProjectiveSpaceDatumClass n S where
  toFun := toProjectiveSpaceDatumClass n
  invFun := ofProjectiveSpaceDatumClass n
  left_inv := ofProjectiveSpaceDatumClass_toProjectiveSpaceDatumClass n
  right_inv := toProjectiveSpaceDatumClass_ofProjectiveSpaceDatumClass n

/-- The equivalence between rank-one quotient classes and projective-space datum classes is
natural under pullback of schemes. -/
theorem selfSuccDatumClassEquiv_naturality (n : ℕ) {S T : Scheme.{u}ᵒᵖ}
    (f : S ⟶ T) :
    (functor n (n + 1)).map f ≫
        (selfSuccDatumClassEquiv n T.unop).toIso.hom =
      (selfSuccDatumClassEquiv n S.unop).toIso.hom ≫
        (ProjectiveSpaceDatumClass.functor n).map f := sorry

/-- The Grassmannian functor in successive dimensions is naturally isomorphic to the functor
of projective-space data. -/
def selfSuccFunctorIso (n : ℕ) :
    functor.{u} n (n + 1) ≅ ProjectiveSpaceDatumClass.functor.{u} n :=
  NatIso.ofComponents
    (fun S ↦ (selfSuccDatumClassEquiv n S.unop).toIso)
    (fun f ↦ selfSuccDatumClassEquiv_naturality n f)

namespace Model

/-- An explicit model of the Grassmannian functor in successive dimensions is isomorphic to
integral projective space relative to an explicit representation of projective-space data. -/
def selfSuccIsoProjectiveSpace (n : ℕ) (hn : 0 < n)
    (P : Model n (n + 1) hn (Nat.lt_succ_self n))
    (R : (ProjectiveSpaceDatumClass.functor n).RepresentableBy
      (ProjectiveSpace.scheme ℤ n)) :
    P.scheme ≅ ProjectiveSpace.scheme ℤ n :=
  (P.isRepresentedBy.representableBy.ofIso (selfSuccFunctorIso n)).uniqueUpToIso R

/-- The forward morphism of the comparison isomorphism classifies the projective-space datum
obtained from the universal rank-one quotient. -/
theorem selfSuccIsoProjectiveSpace_hom_classifies (n : ℕ) (hn : 0 < n)
    (P : Model n (n + 1) hn (Nat.lt_succ_self n))
    (R : (ProjectiveSpaceDatumClass.functor n).RepresentableBy
      (ProjectiveSpace.scheme ℤ n)) :
    R.homEquiv (selfSuccIsoProjectiveSpace n hn P R).hom =
      (selfSuccFunctorIso n).hom.app (Opposite.op P.scheme) P.point := sorry

end Model

end Grassmannian

end AlgebraicGeometry
