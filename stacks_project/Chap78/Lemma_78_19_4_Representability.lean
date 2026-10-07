module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.Representability
public import stacks_project.Chap78.Definition_78_19_1_QuotientSheaf

/-!
# Representability of quotient sheaves of algebraic-space pre-relations

This compatibility module checks the shared comparison `(t, s) : R ⟶ U ×_M U` and
descent `U/R ⟶ uliftSheaf M` induced by an equalizing morphism `q : U ⟶ M`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits ConcreteCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientDesc_respects :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q) {T : Over S}
    {x y : U.left.functorOfPoints.obj (op T)} (hxy : P.schemePointRel T x y),
    q.app (op T) x = q.app (op T) y)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientPresheafDesc :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q),
    P.quotientPresheaf ⟶ M.functorOfPoints)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientPresheafDesc_mk :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q) {T : Over S}
    (x : U.left.functorOfPoints.obj (op T)),
    (P.quotientPresheafDesc q h_equalizes).app (op T) (Quot.mk (P.schemePointRel T) x) =
      q.app (op T) x)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.kernelPairLift :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q),
    P.left.left ⟶ pullback q q)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.kernelPairLift_fst :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q),
    P.kernelPairLift q h_equalizes ≫ pullback.fst q q = P.t.left)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.kernelPairLift_snd :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q),
    P.kernelPairLift q h_equalizes ≫ pullback.snd q q = P.s.left)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheafDesc :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q),
    P.quotientSheaf ⟶ uliftSheaf M)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheafDesc_quotientMap :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q),
    P.quotientMap ≫ P.quotientSheafDesc q h_equalizes = uliftSheafMap q)

end AlgebraicGeometry.AlgebraicSpace.PreRelation
