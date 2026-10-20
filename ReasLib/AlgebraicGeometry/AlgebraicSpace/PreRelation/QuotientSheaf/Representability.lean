module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf

/-!
# Representability of quotient sheaves of algebraic-space pre-relations

An equalizing morphism induces a comparison from the quotient sheaf to the sheaf of
points of its target. Local surjectivity of this morphism and of the induced kernel-pair
map makes the comparison an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits ConcreteCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- Composing with an equalizing morphism identifies scheme-valued points related by a
pre-relation. -/
theorem quotientDesc_respects {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q) {T : Over S}
    {x y : U.left.functorOfPoints.obj (op T)} (hxy : P.schemePointRel T x y) :
    q.app (op T) x = q.app (op T) y := sorry

/-- The canonical map from the quotient presheaf to the functor of points of `M` induced by
an equalizing morphism `q : U.left ⟶ M`. -/
def quotientPresheafDesc {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q) :
    P.quotientPresheaf ⟶ M.functorOfPoints where
  app T :=
    TypeCat.ofHom <|
      Quot.lift (fun point ↦ q.app T point) fun _ _ h_related ↦
        P.quotientDesc_respects q h_equalizes h_related
  naturality := sorry

/-- The presheaf descent map sends the quotient class represented by `x` to `q.app (op T) x`. -/
theorem quotientPresheafDesc_mk {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q) {T : Over S}
    (x : U.left.functorOfPoints.obj (op T)) :
    (P.quotientPresheafDesc q h_equalizes).app (op T) (Quot.mk (P.schemePointRel T) x) =
      q.app (op T) x := sorry

/-- The map `(t, s) : R ⟶ U ×_M U` induced by an equalizing morphism. -/
noncomputable def kernelPairLift {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q) :
    P.left.left ⟶ pullback q q :=
  pullback.lift P.t.left P.s.left h_equalizes

/-- The first projection of `kernelPairLift` is `P.t.left`. -/
theorem kernelPairLift_fst {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q) :
    P.kernelPairLift q h_equalizes ≫ pullback.fst q q = P.t.left := sorry

/-- The second projection of `kernelPairLift` is `P.s.left`. -/
theorem kernelPairLift_snd {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q) :
    P.kernelPairLift q h_equalizes ≫ pullback.snd q q = P.s.left := sorry

/-- The canonical comparison from the quotient sheaf `U/R` to the sheaf of points of `M`
induced by an equalizing morphism `q : U.left ⟶ M`. -/
noncomputable def quotientSheafDesc {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q) :
    P.quotientSheaf ⟶ toSheaf.obj M :=
  ((sheafificationAdjunction (Scheme.fppfTopology.over S) (Type (u + 1))).homEquiv
    (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}) (toSheaf.obj M)).symm
      (Functor.whiskerRight (P.quotientPresheafDesc q h_equalizes) uliftFunctor.{u + 1, u})

/-- The quotient comparison factors the sheaf morphism induced by `q`. -/
theorem quotientSheafDesc_quotientMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q) :
    P.quotientMap ≫ P.quotientSheafDesc q h_equalizes = toSheaf.map q := sorry

/-- An equalizing morphism whose sheaf map and induced kernel-pair map are fppf-locally
surjective identifies the quotient sheaf with the sheaf of points of its target. -/
theorem quotientSheafDesc_isIso_of_locallySurjective {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) {M : AlgebraicSpace S}
    (q : U.left ⟶ M) (h_equalizes : P.t.left ≫ q = P.s.left ≫ q)
    (h_q : Sheaf.IsLocallySurjective (toSheaf.map q))
    (h_kernel : Sheaf.IsLocallySurjective (toSheaf.map (P.kernelPairLift q h_equalizes))) :
    IsIso (P.quotientSheafDesc q h_equalizes) := sorry

/-- Locally surjective equalizing morphisms make the quotient-sheaf comparison an
isomorphism. -/
instance quotientSheafDesc_isIso {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q)
    [h_q : Sheaf.IsLocallySurjective (toSheaf.map q)]
    [h_kernel : Sheaf.IsLocallySurjective (toSheaf.map (P.kernelPairLift q h_equalizes))] :
    IsIso (P.quotientSheafDesc q h_equalizes) :=
  quotientSheafDesc_isIso_of_locallySurjective P q h_equalizes h_q h_kernel

end AlgebraicGeometry.AlgebraicSpace.PreRelation
