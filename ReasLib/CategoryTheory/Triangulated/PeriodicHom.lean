/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Rotate
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.TriangleShift
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Matress

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated ComplexShape HomologicalComplex₂ Limits

universe v u

namespace HomologicalComplex₂

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Matress

/-- The object in degree `p = 3n+i` is the `i`th triangle object shifted by `n`. -/
def triangleObject (T : Triangle D) (p : ℤ) : D :=
  (if p % 3 = 0 then T.obj₁ else if p % 3 = 1 then T.obj₂ else T.obj₃)⟦p / 3⟧

-- Local declaration justification (metaprogramming implementation): Export the private equality proof for use in exposed object transports.
set_option backward.privateInPublic true in
/-- Quotient and remainder identify the next triangle object, including at negative degrees. -/
private theorem triangleIndexSucc (T : Triangle D) (p : ℤ) :
    triangleObject T (p + 1) =
      if p % 3 = 0 then T.obj₂⟦p / 3⟧
      else if p % 3 = 1 then T.obj₃⟦p / 3⟧ else T.obj₁⟦p / 3 + 1⟧ := sorry

-- Local declaration justification (metaprogramming implementation): Export the private period equality proof for use in exposed object transports.
set_option backward.privateInPublic true in
/-- Adding three preserves the remainder and increments the quotient. -/
private theorem triangleIndexPeriod (p : ℤ) :
    ((p + 3) % 3, (p + 3) / 3) = (p % 3, p / 3 + 1) := sorry

-- Local declaration justification (metaprogramming implementation): The exposed transition uses the private successor equality only as a cast proof.
set_option backward.privateInPublic true in
/-- Consecutive objects are connected by the corresponding shifted triangle morphism. -/
def triangleMap (T : Triangle D) (p : ℤ) :
    triangleObject T p ⟶ triangleObject T (p + 1) :=
  let next := if p % 3 = 0 then T.obj₂⟦p / 3⟧
    else if p % 3 = 1 then T.obj₃⟦p / 3⟧ else T.obj₁⟦p / 3 + 1⟧
  let transition : triangleObject T p ⟶ next :=
    if h₀ : p % 3 = 0 then
      (shiftFunctor D (p / 3)).map (eqToHom (if_pos h₀)) ≫
        (shiftFunctor D (p / 3)).map T.mor₁ ≫ eqToHom (if_pos h₀).symm
    else if h₁ : p % 3 = 1 then
      (shiftFunctor D (p / 3)).map (eqToHom ((if_neg h₀).trans (if_pos h₁))) ≫
        (shiftFunctor D (p / 3)).map T.mor₂ ≫
          eqToHom ((if_neg h₀).trans (if_pos h₁)).symm
    else
      (shiftFunctor D (p / 3)).map (eqToHom ((if_neg h₀).trans (if_neg h₁))) ≫
        (shiftFunctor D (p / 3)).map T.mor₃ ≫
          ((shiftFunctorAdd' D 1 (p / 3) (p / 3 + 1) (add_comm _ _)).app T.obj₁).inv ≫
            eqToHom ((if_neg h₀).trans (if_neg h₁)).symm
  transition ≫ eqToHom (triangleIndexSucc T p).symm

-- Local declaration justification (metaprogramming implementation): The exposed period comparison uses the private index equality only as a cast proof.
set_option backward.privateInPublic true in
/-- The canonical comparison from degree `p+3` to the shift of degree `p`. -/
def triangleObjectPeriodIso (T : Triangle D) (p : ℤ) :
    triangleObject T (p + 3) ≅ (triangleObject T p)⟦(1 : ℤ)⟧ :=
  eqToIso (congrArg (fun index : ℤ × ℤ =>
    (if index.1 = 0 then T.obj₁ else if index.1 = 1 then T.obj₂ else T.obj₃)⟦index.2⟧)
      (triangleIndexPeriod p)) ≪≫
    (shiftFunctorAdd D (p / 3) 1).app
      (if p % 3 = 0 then T.obj₁ else if p % 3 = 1 then T.obj₂ else T.obj₃)

/-- Normalize the first two unsigned periodic arrows; the third arrow carries
the rotation-and-shift sign at the starting degree. -/
def normalizedTriangle (T : Triangle D) (a : ℤ) : Triangle D :=
  Triangle.mk (triangleMap T a) (triangleMap T (a + 1))
    (a.negOnePow •
      (eqToHom (congrArg (triangleObject T) (show a + 1 + 1 = a + 2 by omega)) ≫
        triangleMap T (a + 2) ≫
        eqToHom (congrArg (triangleObject T) (show a + 2 + 1 = a + 3 by omega)) ≫
        (triangleObjectPeriodIso T a).hom))

/-- Rotations contribute (-1)^i and shift by n contributes (-1)^n for
a=3n+i; after normalizing the first two arrows the third sign is (-1)^a. -/
theorem normalizedTriangle_distinguished {T : Triangle D}
    (hT : T ∈ distTriang D) (a : ℤ) : normalizedTriangle T a ∈ distTriang D := sorry

/-- The degree-zero transition is the first morphism, under zero-shift comparisons. -/
theorem triangleMap_zero (T : Triangle D) :
    (shiftZero ℤ T.obj₁).inv ≫ triangleMap T 0 ≫ (shiftZero ℤ T.obj₂).hom = T.mor₁ := sorry

/-- The degree-one transition is the second morphism, under zero-shift comparisons. -/
theorem triangleMap_one (T : Triangle D) :
    (shiftZero ℤ T.obj₂).inv ≫ triangleMap T 1 ≫ (shiftZero ℤ T.obj₃).hom = T.mor₂ := sorry

/-- The degree-two transition is the connecting morphism, under canonical shift comparisons. -/
theorem triangleMap_two (T : Triangle D) :
    (shiftZero ℤ T.obj₃).inv ≫ triangleMap T 2 ≫ (triangleObjectPeriodIso T 0).hom ≫
      (shiftFunctor D 1).map (shiftZero ℤ T.obj₁).hom = T.mor₃ := sorry

/-- Consecutive transitions of a distinguished triangle compose to zero. -/
theorem triangleMap_comp_zero {T : Triangle D} (hT : T ∈ distTriang D) (p : ℤ) :
    triangleMap T p ≫ triangleMap T (p + 1) = 0 := sorry

/-- Transition maps commute with the unsigned canonical object-period comparison. -/
theorem triangleMap_periodic (T : Triangle D) (p : ℤ) :
    triangleMap T (p + 3) ≫
        eqToHom (congrArg (triangleObject T) (add_right_comm p 3 1)) ≫
          (triangleObjectPeriodIso T (p + 1)).hom =
      (triangleObjectPeriodIso T p).hom ≫ (shiftFunctor D 1).map (triangleMap T p) := sorry

/-- The additive Hom-group term `K^{p,q} = Hom (X^{-p}, Y^q)` of two triangles. -/
def term (X Y : Triangle D) (p q : ℤ) : AddCommGrpCat :=
  AddCommGrpCat.of (triangleObject X (-p) ⟶ triangleObject Y q)

/-- Precomposition by a morphism in `D`, viewed as an additive-group morphism. -/
def precomposeHom {A B C : D} (f : A ⟶ B) :
    AddCommGrpCat.of (B ⟶ C) ⟶ AddCommGrpCat.of (A ⟶ C) :=
  AddCommGrpCat.ofHom
    { toFun := fun g => f ≫ g
      map_zero' := comp_zero
      map_add' := fun g h => Preadditive.comp_add _ _ _ _ g h }

/-- Postcomposition by a morphism in `D`, viewed as an additive-group morphism. -/
def postcomposeHom {A B C : D} (f : B ⟶ C) :
    AddCommGrpCat.of (A ⟶ B) ⟶ AddCommGrpCat.of (A ⟶ C) :=
  AddCommGrpCat.ofHom
    { toFun := fun g => g ≫ f
      map_zero' := zero_comp
      map_add' := fun g h => Preadditive.add_comp _ _ _ g h _ }

/-- The index identity used to align a source degree with the periodic shift. -/
theorem periodicDomainSourceEq (p : ℤ) : -p = (-(p + 3)) + 3 := sorry

/-- The index identity used to align a target degree with the periodic shift. -/
theorem periodicCodomainSourceEq (q : ℤ) : q = (q - 3) + 3 := sorry

/-- The canonical periodic isomorphism on the source object in the Hom term. -/
def periodicDomainIso (X : Triangle D) (p : ℤ) :
    triangleObject X (-p) ≅ triangleObject X (-(p + 3))⟦(1 : ℤ)⟧ :=
  eqToIso (congrArg (triangleObject X) (periodicDomainSourceEq p)) ≪≫
    triangleObjectPeriodIso X (-(p + 3))

/-- The canonical periodic isomorphism on the target object in the Hom term. -/
def periodicCodomainIso (Y : Triangle D) (q : ℤ) :
    triangleObject Y q ≅ triangleObject Y (q - 3)⟦(1 : ℤ)⟧ :=
  eqToIso (congrArg (triangleObject Y) (periodicCodomainSourceEq q)) ≪≫
    triangleObjectPeriodIso Y (q - 3)

/-- The forward action of the shift on a morphism. -/
def shiftHom {A B : D} (f : A ⟶ B) :
    A⟦(1 : ℤ)⟧ ⟶ B⟦(1 : ℤ)⟧ :=
  (shiftFunctor D 1).map f

/-- Additivity of the forward shift action on morphisms. -/
theorem shiftHom_add {A B : D} (f g : A ⟶ B) :
    shiftHom (f + g) = shiftHom f + shiftHom g := sorry

/-- The inverse action of the shift on a shifted morphism. -/
def unshiftHom {A B : D} (f : A⟦(1 : ℤ)⟧ ⟶ B⟦(1 : ℤ)⟧) : A ⟶ B :=
  (shiftShiftNeg A (1 : ℤ)).inv ≫ (shiftFunctor D (-1)).map f ≫
    (shiftShiftNeg B (1 : ℤ)).hom

/-- Additivity of the inverse shift action on shifted morphisms. -/
theorem unshiftHom_add {A B : D}
    (f g : A⟦(1 : ℤ)⟧ ⟶ B⟦(1 : ℤ)⟧) :
    unshiftHom (f + g) = unshiftHom f + unshiftHom g := sorry

/-- The forward shift action as an additive-group morphism. -/
def shiftHomMap (A B : D) :
    AddCommGrpCat.of (A ⟶ B) ⟶ AddCommGrpCat.of (A⟦(1 : ℤ)⟧ ⟶ B⟦(1 : ℤ)⟧) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' shiftHom (shiftHom_add (A := A) (B := B)))

/-- The inverse shift action as an additive-group morphism. -/
def unshiftHomMap (A B : D) :
    AddCommGrpCat.of (A⟦(1 : ℤ)⟧ ⟶ B⟦(1 : ℤ)⟧) ⟶ AddCommGrpCat.of (A ⟶ B) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' unshiftHom (unshiftHom_add (A := A) (B := B)))

/-- The canonical map on Hom groups induced by the periodic object isomorphisms. -/
def canonicalHomTransportHom (P Q : Triangle D) (p q : ℤ) :
    term P Q p q ⟶ term P Q (p + 3) (q - 3) :=
  precomposeHom (periodicDomainIso P p).inv ≫
    postcomposeHom (periodicCodomainIso Q q).hom ≫
      unshiftHomMap (triangleObject P (-(p + 3))) (triangleObject Q (q - 3))

/-- The inverse of the canonical map on Hom groups. -/
def canonicalHomTransportInv (P Q : Triangle D) (p q : ℤ) :
    term P Q (p + 3) (q - 3) ⟶ term P Q p q :=
  shiftHomMap (triangleObject P (-(p + 3))) (triangleObject Q (q - 3)) ≫
    postcomposeHom (periodicCodomainIso Q q).inv ≫
      precomposeHom (periodicDomainIso P p).hom

/-- The canonical Hom transport and its inverse compose to the identity. -/
theorem canonicalHomTransport_hom_inv (P Q : Triangle D) (p q : ℤ) :
    canonicalHomTransportHom P Q p q ≫ canonicalHomTransportInv P Q p q =
      𝟙 (term P Q p q) := sorry

/-- The inverse canonical Hom transport and its transport compose to the identity. -/
theorem canonicalHomTransport_inv_hom (P Q : Triangle D) (p q : ℤ) :
    canonicalHomTransportInv P Q p q ≫ canonicalHomTransportHom P Q p q =
      𝟙 (term P Q (p + 3) (q - 3)) := sorry

/-- The canonical Hom transport induced by the periodic object isomorphisms. -/
def canonicalHomTransport (P Q : Triangle D) (p q : ℤ) :
    term P Q p q ≅ term P Q (p + 3) (q - 3) :=
  { hom := canonicalHomTransportHom P Q p q
    inv := canonicalHomTransportInv P Q p q
    hom_inv_id := canonicalHomTransport_hom_inv P Q p q
    inv_hom_id := canonicalHomTransport_inv_hom P Q p q }

/-- Horizontal differential in the successor-index case. -/
def d₁Succ (P Q : Triangle D)
    (p p' q : ℤ) (h : p' = p + 1) : term P Q p q ⟶ term P Q p' q :=
  precomposeHom (triangleMap P (-(p + 1)) ≫
    eqToHom (congrArg (triangleObject P)
      ((congrArg (fun index : ℤ => index + 1)
        (Int.neg_add : -(p + 1) = -p + -(1 : ℤ))).trans
        (Int.neg_add_cancel_right (-p) 1)))) ≫
      eqToHom (congrArg (fun r => term P Q r q) h.symm)

/-- Vertical differential in the successor-index case. -/
def d₂Succ (P Q : Triangle D)
    (p q q' : ℤ) (h : q' = q + 1) : term P Q p q ⟶ term P Q p q' :=
  postcomposeHom (triangleMap Q q) ≫ eqToHom (congrArg (fun r => term P Q p r) h.symm)

/-- The horizontal differential, given by precomposition with the `X` transition map. -/
def d₁ (P Q : Triangle D)
    (p p' q : ℤ) : term P Q p q ⟶ term P Q p' q :=
  if h : p' = p + 1 then d₁Succ P Q p p' q h else 0

/-- The vertical differential, given by postcomposition with the `Y` transition map. -/
def d₂ (P Q : Triangle D)
    (p q q' : ℤ) : term P Q p q ⟶ term P Q p q' :=
  if h : q' = q + 1 then d₂Succ P Q p q q' h else 0

/-- Shape-zero law for the horizontal differential used by `ofGradedObject`. -/
theorem d₁_shape (P Q : Triangle D)
    (p p' : ℤ) (h : ¬ (up ℤ).Rel p p') (q : ℤ) : d₁ P Q p p' q = 0 := sorry

/-- Shape-zero law for the vertical differential used by `ofGradedObject`. -/
theorem d₂_shape (P Q : Triangle D)
    (p q q' : ℤ) (h : ¬ (up ℤ).Rel q q') : d₂ P Q p q q' = 0 := sorry

/-- Consecutive horizontal differentials compose to zero. -/
theorem d₁_comp_d₁ (P Q : Triangle D) (hP : P ∈ distTriang D)
    (p p' p'' q : ℤ) : d₁ P Q p p' q ≫ d₁ P Q p' p'' q = 0 := sorry

/-- Consecutive vertical differentials compose to zero. -/
theorem d₂_comp_d₂ (P Q : Triangle D) (hQ : Q ∈ distTriang D)
    (p q q' q'' : ℤ) : d₂ P Q p q q' ≫ d₂ P Q p q' q'' = 0 := sorry

/-- The horizontal and vertical differentials commute. -/
theorem d₁_d₂_comm (P Q : Triangle D)
    (p p' q q' : ℤ) :
    d₁ P Q p p' q ≫ d₂ P Q p' q q' = d₂ P Q p q q' ≫ d₁ P Q p p' q' := sorry

/-- The Hom double complex attached to two distinguished triangles. -/
def complex {P Q : Triangle D} (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) :
    HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ) :=
  HomologicalComplex₂.ofGradedObject (up ℤ) (up ℤ)
    (fun i : ℤ × ℤ => term P Q i.1 i.2)
    (fun p p' q => d₁ P Q p p' q) (fun p q q' => d₂ P Q p q q')
    (d₁_shape P Q) (d₂_shape P Q)
    (d₁_comp_d₁ P Q hP) (d₂_comp_d₂ P Q hQ) (d₁_d₂_comm P Q)

/-- Parity-signed Hom transport commutes with the horizontal differential of the signed shift. -/
theorem periodHom_horizontal {P Q : Triangle D}
    (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) (p p' q : ℤ)
    (h : (up ℤ).Rel p p') :
    ((p + q).negOnePow • canonicalHomTransportHom P Q p q) ≫
        (((complex hP hQ).bidegreeShift 3 (-3)).d p p').f q =
      ((complex hP hQ).d p p').f q ≫
        ((p' + q).negOnePow • canonicalHomTransportHom P Q p' q) := sorry

/-- Parity-signed Hom transport commutes with the vertical differential of the signed shift. -/
theorem periodHom_vertical {P Q : Triangle D}
    (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) (p q q' : ℤ)
    (h : (up ℤ).Rel q q') :
    ((p + q).negOnePow • canonicalHomTransportHom P Q p q) ≫
        (((complex hP hQ).bidegreeShift 3 (-3)).X p).d q q' =
      ((complex hP hQ).X p).d q q' ≫
        ((p + q').negOnePow • canonicalHomTransportHom P Q p q') := sorry

/-- The morphism from a Hom double complex to its signed `(3,-3)` shift. -/
def periodHom {P Q : Triangle D} (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) :
    complex hP hQ ⟶ (complex hP hQ).bidegreeShift 3 (-3) :=
  HomologicalComplex₂.homMk
    (fun index => (index.1 + index.2).negOnePow •
      canonicalHomTransportHom P Q index.1 index.2)
    (periodHom_horizontal hP hQ) (periodHom_vertical hP hQ)

/-- Inverse parity-signed transport commutes with the horizontal differential. -/
theorem periodInv_horizontal {P Q : Triangle D}
    (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) (p p' q : ℤ)
    (h : (up ℤ).Rel p p') :
    ((p + q).negOnePow • canonicalHomTransportInv P Q p q) ≫
        ((complex hP hQ).d p p').f q =
      (((complex hP hQ).bidegreeShift 3 (-3)).d p p').f q ≫
        ((p' + q).negOnePow • canonicalHomTransportInv P Q p' q) := sorry

/-- Inverse parity-signed transport commutes with the vertical differential. -/
theorem periodInv_vertical {P Q : Triangle D}
    (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) (p q q' : ℤ)
    (h : (up ℤ).Rel q q') :
    ((p + q).negOnePow • canonicalHomTransportInv P Q p q) ≫
        ((complex hP hQ).X p).d q q' =
      (((complex hP hQ).bidegreeShift 3 (-3)).X p).d q q' ≫
        ((p + q').negOnePow • canonicalHomTransportInv P Q p q') := sorry

/-- The inverse morphism from the signed `(3,-3)` shift to the Hom double complex. -/
def periodInv {P Q : Triangle D} (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) :
    (complex hP hQ).bidegreeShift 3 (-3) ⟶ complex hP hQ :=
  HomologicalComplex₂.homMk
    (fun index => (index.1 + index.2).negOnePow •
      canonicalHomTransportInv P Q index.1 index.2)
    (periodInv_horizontal hP hQ) (periodInv_vertical hP hQ)

/-- Forward and inverse signed period morphisms compose to the identity. -/
theorem period_hom_inv {P Q : Triangle D}
    (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) :
    periodHom hP hQ ≫ periodInv hP hQ = 𝟙 (complex hP hQ) := sorry

/-- Inverse and forward signed period morphisms compose to the identity. -/
theorem period_inv_hom {P Q : Triangle D}
    (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) :
    periodInv hP hQ ≫ periodHom hP hQ =
      𝟙 ((complex hP hQ).bidegreeShift 3 (-3)) := sorry

/-- The explicit signed `(3,-3)` period isomorphism of the Hom double complex. -/
def period {P Q : Triangle D} (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) :
    complex hP hQ ≅ (complex hP hQ).bidegreeShift 3 (-3) :=
  { hom := periodHom hP hQ
    inv := periodInv hP hQ
    hom_inv_id := period_hom_inv hP hQ
    inv_hom_id := period_inv_hom hP hQ }

/-- Removing the parity sign from the complex period recovers canonical unsigned Hom transport. -/
theorem periodicCompatible {P Q : Triangle D}
    (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) (p q : ℤ) :
    periodComponent (period hP hQ) p q (p + 3) (q - 3) rfl rfl =
      canonicalHomTransport P Q p q := sorry

/-- Every column of the Hom double complex of distinguished triangles is exact. -/
theorem verticalExact {P Q : Triangle D}
    (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) :
    ∀ p : ℤ, ((complex hP hQ).X p).Acyclic := sorry

/-- Every row of the Hom double complex of distinguished triangles is exact. -/
theorem horizontalExact {P Q : Triangle D}
    (hP : P ∈ distTriang D) (hQ : Q ∈ distTriang D) :
    ∀ q : ℤ, ((complex hP hQ).flip.X q).Acyclic := sorry

/-- The signed TR3 filler property for unsigned shifted transition maps. The
source degree -p and target degree q contribute the factor (-1)^(p+q). -/
theorem fillerOfDistinguished {X Y : Triangle D}
    (hX : X ∈ distTriang D) (hY : Y ∈ distTriang D) :
    ∀ (p q : ℤ) (α : ((complex hX hY).X p).X q)
      (β : ((complex hX hY).X (p - 1)).X (q + 1)),
      ((complex hX hY).X p).d q (q + 1) α =
          ((complex hX hY).d (p - 1) p).f (q + 1) β →
        ∃ γ : ((complex hX hY).X (p - 2)).X (q + 2),
          ((complex hX hY).d (p - 2) (p - 1)).f (q + 2) γ =
              ((complex hX hY).X (p - 1)).d (q + 1) (q + 2) β ∧
            (periodComponent (period hX hY) (p - 2) (q + 3) (p + 1) q
                (filler_index₁ p) (filler_index₂ q)).hom
                (((complex hX hY).X (p - 2)).d (q + 2) (q + 3) γ) =
              fillerSign p q • ((complex hX hY).d p (p + 1)).f q α := sorry

/-- The actual periodic Hom double complex is a matress with the corrected
signed TR3 convention, with no extra hypotheses on the triangles. -/
theorem fromTriangles {X Y : Triangle D}
    (hX : X ∈ distTriang D) (hY : Y ∈ distTriang D) :
    Matress (complex hX hY) (period hX hY) :=
  fromProperties _ _ (verticalExact hX hY) (horizontalExact hX hY)
    (fillerOfDistinguished hX hY)

end Matress

end HomologicalComplex₂

end
