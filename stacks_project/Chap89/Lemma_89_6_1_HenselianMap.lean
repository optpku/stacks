/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Definition_68_11_2_ResidueField
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing
public import stacks_project.Chap68.Lemma_68_17_7
public import stacks_project.Chap89.Lemma_89_6_1_BaseChange

/-!
# Comparison of henselian local rings after base change to the completion

An elementary étale neighbourhood of `(X, p)` pulls back along
`Y = X ×_{Spec(A)} Spec(A^∧)` to an elementary étale neighbourhood of
`(Y, q)`, and the resulting maps on global sections induce a homomorphism of
henselian local rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {X : AlgebraicSpace (Spec (.of A))} [IsDecent X]
variable (q : Points (completionBaseChange A X))

namespace EtaleNeighborhood.Elementary

/-- The scheme `U ×_{Spec(A)} Spec(A^∧)` obtained by pulling back an elementary
étale neighbourhood of the image of `q` along the `m`-adic completion. -/
abbrev completionPullbackScheme
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    Scheme.{u} :=
  pullback U.obj.toOver.hom (specAdicCompletionSchemeHom A)

/-- The scheme `U ×_{Spec(A)} Spec(A^∧)` as an object of `Over Spec(A)`. -/
abbrev completionPullbackOver
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    Over (Spec (.of A)) :=
  Over.mk
    (pullback.fst U.obj.toOver.hom (specAdicCompletionSchemeHom A) ≫
      U.obj.toOver.hom)

/-- The morphism `U ×_{Spec(A)} Spec(A^∧) ⟶ U` of algebraic spaces over
`Spec(A)`. -/
def completionPullbackToNeighborhood
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    ofOver (completionPullbackOver q U) ⟶ ofOver U.obj.toOver :=
  ofOverHomMk
    (pullback.fst U.obj.toOver.hom (specAdicCompletionSchemeHom A)) rfl

/-- The morphism `U ×_{Spec(A)} Spec(A^∧) ⟶ Spec(A^∧)` of algebraic spaces over
`Spec(A)`. -/
def completionPullbackToCompletion
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    ofOver (completionPullbackOver q U) ⟶ specAdicCompletion A :=
  ofOverHomMk (pullback.snd U.obj.toOver.hom (specAdicCompletionSchemeHom A))
    (pullback.condition :
        pullback.fst U.obj.toOver.hom (specAdicCompletionSchemeHom A) ≫
            U.obj.toOver.hom =
          pullback.snd U.obj.toOver.hom (specAdicCompletionSchemeHom A) ≫
            specAdicCompletionSchemeHom A).symm

/-- The two legs from `U ×_{Spec(A)} Spec(A^∧)` to `X` and to `Spec(A^∧)` agree
over `Spec(A)`. -/
theorem completionPullbackHom_w
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    completionPullbackToNeighborhood q U ≫ U.obj.hom ≫ toBase X =
      completionPullbackToCompletion q U ≫ specAdicCompletionHom A :=
  sorry

/-- The morphism `U ×_{Spec(A)} Spec(A^∧) ⟶ Y` of algebraic spaces over
`Spec(A)`. -/
def completionPullbackHom
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    ofOver (completionPullbackOver q U) ⟶ completionBaseChange A X :=
  pullback.lift (completionPullbackToNeighborhood q U ≫ U.obj.hom)
    (completionPullbackToCompletion q U) (completionPullbackHom_w q U)

/-- Base change of an étale neighbourhood along `Spec(A^∧) ⟶ Spec(A)` remains
étale over `Y`. -/
instance instEtale_completionPullbackHom
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    Etale (completionPullbackHom q U) :=
  sorry

/-- The pulled-back neighbourhood as an object of the small étale site of `Y`. -/
def completionPullbackSite
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    smallEtaleSite (completionBaseChange A X) :=
  smallEtaleSite.mk (completionPullbackHom q U)

/-- The residue-field representative of `q` maps to the same point of `X` as the
selected point of an elementary neighbourhood of the image of `q`. -/
theorem residuePoint_map_fst_eq
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    Points.mk
        ((FieldValuedPoint.residuePoint q).map (completionBaseChange.fst A X)) =
      Points.mk (residuePoint U.obj) :=
  sorry

/-- Unique factorization of the residue-field representative of `q` through the
elementary monomorphism `Spec(κ(u)) ⟶ X`. -/
def factorThroughNeighborhood
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    FieldValuedPoint.Factorization
      ((FieldValuedPoint.residuePoint q).map (completionBaseChange.fst A X))
      (residuePoint U.obj) :=
  let h := FieldValuedPoint.unique_factorization_of_mono U.property
    (residuePoint_map_fst_eq q U)
  Classical.choice h.1

/-- The scheme morphism `Spec(κ(q)) ⟶ U` obtained by composing the unique
factorization through `Spec(κ(u))` with `Spec(κ(u)) ⟶ U`. -/
def toNeighborhoodSchemeHom
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    Spec (.of (FieldValuedPoint.residuePoint q).K) ⟶ U.obj.scheme :=
  (factorThroughNeighborhood q U).schemeHom ≫
    (Scheme.FieldValuedPoint.residuePoint U.obj.point).hom

/-- The scheme morphism `Spec(κ(q)) ⟶ Spec(A^∧)` induced by the residue-field
representative of `q`. -/
def toCompletionSchemeHom :
    Spec (.of (FieldValuedPoint.residuePoint q).K) ⟶
      Spec (.of (AdicCompletion (maximalIdeal A) A)) :=
  (FieldValuedPoint.toScheme
    ((FieldValuedPoint.residuePoint q).map
      (completionBaseChange.snd A X))).hom

/-- The two induced maps `Spec(κ(q)) ⟶ U` and `Spec(κ(q)) ⟶ Spec(A^∧)` agree
over `Spec(A)`. -/
theorem toPullbackSchemeHom_w
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    toNeighborhoodSchemeHom q U ≫ U.obj.toOver.hom =
      toCompletionSchemeHom q ≫ specAdicCompletionSchemeHom A :=
  sorry

/-- The induced scheme morphism `Spec(κ(q)) ⟶ U ×_{Spec(A)} Spec(A^∧)` of the
canonical point `v = (u, q)`. -/
def toPullbackSchemeHom
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    Spec (.of (FieldValuedPoint.residuePoint q).K) ⟶
      completionPullbackScheme q U :=
  pullback.lift (toNeighborhoodSchemeHom q U) (toCompletionSchemeHom q)
    (toPullbackSchemeHom_w q U)

/-- The induced map `Spec(κ(q)) ⟶ U ×_{Spec(A)} Spec(A^∧)` lies over `Spec(A)`. -/
theorem toPullbackOver_w
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    toPullbackSchemeHom q U ≫ (completionPullbackOver q U).hom =
      (FieldValuedPoint.residuePoint q).structureHom :=
  sorry

/-- The morphism of schemes over `Spec(A)` underlying `v = (u, q)`. -/
def toPullbackOverHom
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    Over.mk (FieldValuedPoint.residuePoint q).structureHom ⟶
      completionPullbackOver q U :=
  Over.homMk (toPullbackSchemeHom q U) (toPullbackOver_w q U)

/-- The field-valued point `v = (u, q)` of `U ×_X Y = U ×_{Spec(A)} Spec(A^∧)`. -/
def toPullbackFieldValuedPoint
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    FieldValuedPoint (ofOver (completionPullbackOver q U)) :=
  FieldValuedPoint.of (FieldValuedPoint.residuePoint q).K
    (FieldValuedPoint.residuePoint q).structureHom
    (ofOverMap (toPullbackOverHom q U))

/-- The selected point `v = (u, q)` of `U ×_{Spec(A)} Spec(A^∧)`. -/
def completionPullbackPoint
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    completionPullbackScheme q U :=
  (ofOver.pointsEquiv (completionPullbackOver q U)).symm
    (Points.mk (toPullbackFieldValuedPoint q U))

/-- The selected pullback point lies over `q`. -/
theorem completionPullbackPoint_spec
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    Points.mapOfOver (completionPullbackHom q U)
        (completionPullbackPoint q U) =
      q :=
  sorry

/-- The pulled-back étale neighbourhood of `(Y, q)`. -/
def completionPullbackNeighborhood
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    EtaleNeighborhood (completionBaseChange A X) q :=
  EtaleNeighborhood.of (completionPullbackSite q U)
    (completionPullbackPoint q U) (completionPullbackPoint_spec q U)

/-- The pulled-back neighbourhood of `(Y, q)` is elementary. -/
theorem completionPullback_isElementary
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    (completionPullbackNeighborhood q U).IsElementary :=
  sorry

/-- The elementary étale neighbourhood of `(Y, q)` obtained by pulling back an
elementary étale neighbourhood of the image of `q` along
`Y = X ×_{Spec(A)} Spec(A^∧)`. -/
def completionPullback
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    Elementary (completionBaseChange A X) q :=
  of (completionPullbackNeighborhood q U) (completionPullback_isElementary q U)

/-- The scheme morphism from the pulled-back elementary neighbourhood to the
original neighbourhood. -/
def completionPullback_schemeHom
    (U : Elementary X (Points.map (completionBaseChange.fst A X) q)) :
    (toScheme (completionBaseChange A X) q).obj (completionPullback q U) ⟶
      (toScheme X (Points.map (completionBaseChange.fst A X) q)).obj U :=
  pullback.fst U.obj.toOver.hom (specAdicCompletionSchemeHom A)

end EtaleNeighborhood.Elementary

namespace henselianLocalRing

/-- The component at an elementary neighbourhood of the cocone inducing
`baseChangeHom`. -/
def baseChangeHom_ι_app
    (U : EtaleNeighborhood.Elementary X
      (Points.map (completionBaseChange.fst A X) q)) :
    (EtaleNeighborhood.Elementary.sections X
          (Points.map (completionBaseChange.fst A X) q)).obj
        (ULiftHom.objUp (op U)) ⟶
      henselianLocalRingCat (completionBaseChange A X) q :=
  (CommRingCat.universeLift.{u, u + 1}).map
      (Scheme.Γ.map
        (EtaleNeighborhood.Elementary.completionPullback_schemeHom q U).op) ≫
    colimit.ι
      (EtaleNeighborhood.Elementary.sections (completionBaseChange A X) q)
      (ULiftHom.objUp
        (op (EtaleNeighborhood.Elementary.completionPullback q U)))

/-- The canonical homomorphism of henselian local rings
`𝒪_{X, p}^h ⟶ 𝒪_{Y, q}^h` induced by base change to the `m`-adic
completion. -/
def baseChangeHom :
    henselianLocalRing X (Points.map (completionBaseChange.fst A X) q) →+*
      henselianLocalRing (completionBaseChange A X) q :=
  (colimit.desc
      (EtaleNeighborhood.Elementary.sections X
        (Points.map (completionBaseChange.fst A X) q))
      { pt := henselianLocalRingCat (completionBaseChange A X) q
        ι :=
          { app := fun j ↦
              baseChangeHom_ι_app q (ULiftHom.objDown j).unop
            naturality := fun _ _ _ ↦ sorry } }).hom

/-- `baseChangeHom` recovers the map on global sections of an elementary étale
neighbourhood after composing with the colimit coprojection. -/
theorem baseChangeHom_comp_ι
    (U : EtaleNeighborhood.Elementary X
      (Points.map (completionBaseChange.fst A X) q)) :
    (baseChangeHom q).comp
        (ι X (Points.map (completionBaseChange.fst A X) q) U) =
      (ι (completionBaseChange A X) q
            (EtaleNeighborhood.Elementary.completionPullback q U)).comp
        (Scheme.Γ.map
            (EtaleNeighborhood.Elementary.completionPullback_schemeHom q
              U).op).hom :=
  sorry

/-- The comparison of henselian local rings along base change to the completion
is a local homomorphism. -/
instance instIsLocalHom_baseChangeHom :
    IsLocalHom (baseChangeHom q) :=
  sorry

end henselianLocalRing

end AlgebraicGeometry.AlgebraicSpace
