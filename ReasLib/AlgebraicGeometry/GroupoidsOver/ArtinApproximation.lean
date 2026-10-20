module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Truncation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.CompleteLocalObject
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.RingTheory.Ideal.AssociatedGraded.DegreeZero

/-!
# Artin approximation data for groupoid fibrations

An approximation of an object `x` over `Spec(R)` at order `N` is a finite type
`S`-algebra `A` with a maximal ideal `m_A`, an object of `X` over `Spec(A)`, an
`S`-isomorphism of `N`-truncations, a compatible restriction isomorphism, and
an isomorphism of associated graded residue algebras.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- Restriction of an object of `X` along `Spec(R ⧸ m_R ^ N) ⟶ Spec(R)`. -/
def restrictionPow {X : GroupoidsOver S} (x : CompleteLocalObject X) (N : ℕ) : X.total :=
  IsPreFibered.pullbackObj x.over_obj (x.base.powOverHom N)

/-- The order-`N` restriction of `x` lies over `Spec(R ⧸ m_R ^ N) ⟶ S`. -/
theorem restrictionPow_over {X : GroupoidsOver S} (x : CompleteLocalObject X) (N : ℕ) :
    X.p.obj (restrictionPow x N) = Over.mk (x.base.powToS N) :=
  sorry

/-- Restriction in `Over S` along `Spec(A ⧸ I ^ N) ⟶ Spec(A)`. -/
def powOverHomOf {A : Type u} [CommRing A] (toS : Spec (CommRingCat.of A) ⟶ S)
    (I : Ideal A) (N : ℕ) :
    Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ N))) ≫ toS) ⟶ Over.mk toS :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ N)))) rfl

/-- The underlying scheme morphism of `powOverHomOf` is the spectrum of the
order-`N` quotient map. -/
theorem powOverHomOf_left {A : Type u} [CommRing A] (toS : Spec (CommRingCat.of A) ⟶ S)
    (I : Ideal A) (N : ℕ) :
    (powOverHomOf toS I N).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ N))) :=
  sorry

/-- The `Over S` morphism induced by an `S`-isomorphism of order-`N` truncations. -/
def isoNOverHom {X : GroupoidsOver S} (x : CompleteLocalObject X) {A : Type u} [CommRing A]
    (toS : Spec (CommRingCat.of A) ⟶ S) (mA : Ideal A) (N : ℕ)
    (e : x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier ^ N ≃+* A ⧸ mA ^ N)
    (w : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ x.base.powToS N =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ toS) :
    Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ toS) ⟶
      Over.mk (x.base.powToS N) :=
  Over.homMk (Spec.map (CommRingCat.ofHom e.toRingHom)) w

/-- The underlying scheme morphism of `isoNOverHom` is the spectrum of the
truncation isomorphism. -/
theorem isoNOverHom_left {X : GroupoidsOver S} (x : CompleteLocalObject X)
    {A : Type u} [CommRing A] (toS : Spec (CommRingCat.of A) ⟶ S) (mA : Ideal A)
    (N : ℕ)
    (e : x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier ^ N ≃+* A ⧸ mA ^ N)
    (w : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ x.base.powToS N =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ toS) :
    (isoNOverHom x toS mA N e w).left = Spec.map (CommRingCat.ofHom e.toRingHom) :=
  sorry

/-- Residue identification `R ⧸ m_R ≃+* A ⧸ m_A` induced by an isomorphism of
order-`N` truncations when `1 ≤ N`. -/
def residueIsoOf {X : GroupoidsOver S} (x : CompleteLocalObject X) {A : Type u} [CommRing A]
    (mA : Ideal A) (N : ℕ)
    (e : x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier ^ N ≃+* A ⧸ mA ^ N)
    (hmap :
      Ideal.map (Ideal.Quotient.mk (mA ^ N)) mA =
        Ideal.map e.toRingHom
          (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal x.base.carrier ^ N))
            (IsLocalRing.maximalIdeal x.base.carrier)))
    (hN : 1 ≤ N) :
    x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier ≃+* A ⧸ mA :=
  (DoubleQuot.quotQuotEquivQuotOfLE
        (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp (Nat.succ_le_iff.mp hN)))).symm.trans
    ((Ideal.quotientEquiv
          (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal x.base.carrier ^ N))
            (IsLocalRing.maximalIdeal x.base.carrier))
          (Ideal.map (Ideal.Quotient.mk (mA ^ N)) mA) e hmap).trans
      (DoubleQuot.quotQuotEquivQuotOfLE
        (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp (Nat.succ_le_iff.mp hN)))))

/-- `residueIsoOf` is the double-quotient identification of residue rings induced by
an order-`N` truncation isomorphism. -/
theorem residueIsoOf_eq {X : GroupoidsOver S} (x : CompleteLocalObject X) {A : Type u}
    [CommRing A] (mA : Ideal A) (N : ℕ)
    (e : x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier ^ N ≃+* A ⧸ mA ^ N)
    (hmap :
      Ideal.map (Ideal.Quotient.mk (mA ^ N)) mA =
        Ideal.map e.toRingHom
          (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal x.base.carrier ^ N))
            (IsLocalRing.maximalIdeal x.base.carrier)))
    (hN : 1 ≤ N) :
    residueIsoOf x mA N e hmap hN =
      (DoubleQuot.quotQuotEquivQuotOfLE
            (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp (Nat.succ_le_iff.mp hN)))).symm.trans
        ((Ideal.quotientEquiv
              (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal x.base.carrier ^ N))
                (IsLocalRing.maximalIdeal x.base.carrier))
              (Ideal.map (Ideal.Quotient.mk (mA ^ N)) mA) e hmap).trans
          (DoubleQuot.quotQuotEquivQuotOfLE
            (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp (Nat.succ_le_iff.mp hN))))) :=
  sorry

/-- Artin approximation data of an object over a complete local finite-type-residue
spectrum, at a fixed positive order. -/
structure ArtinApproximation {X : GroupoidsOver S} (x : CompleteLocalObject X) (N : ℕ) where
  /-- Underlying commutative ring of the approximating finite type `S`-algebra. -/
  carrier : CommRingCat.{u}
  /-- Structure morphism `Spec(A) ⟶ S`. -/
  toS : Spec carrier ⟶ S
  /-- The structure morphism is of finite type. -/
  finiteType : Scheme.Hom.FiniteType toS
  /-- Chosen maximal ideal of the approximating algebra. -/
  maximalIdeal : Ideal carrier
  /-- The chosen ideal is maximal. -/
  isMaximal : maximalIdeal.IsMaximal
  /-- Approximating object of `X`. -/
  object : X.total
  /-- The approximating object lies over `Spec(A) ⟶ S`. -/
  over_obj : X.p.obj object = Over.mk toS
  /-- `S`-isomorphism of order-`N` truncations `R ⧸ m_R ^ N ≃+* A ⧸ m_A ^ N`. -/
  isoN :
    x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier ^ N ≃+*
      carrier ⧸ maximalIdeal ^ N
  /-- `isoN` is an isomorphism of schemes over `S`. -/
  isoN_over :
    Spec.map (CommRingCat.ofHom isoN.toRingHom) ≫ x.base.powToS N =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal ^ N))) ≫ toS
  /-- `isoN` identifies the images of the two maximal ideals in the `N`-truncations. -/
  isoN_map_maximal :
    Ideal.map (Ideal.Quotient.mk (maximalIdeal ^ N)) maximalIdeal =
      Ideal.map isoN.toRingHom
        (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal x.base.carrier ^ N))
          (IsLocalRing.maximalIdeal x.base.carrier))
  /-- Isomorphism of restrictions to the order-`N` truncations. -/
  restrictIso :
    IsPreFibered.pullbackObj over_obj (powOverHomOf toS maximalIdeal N) ⟶ restrictionPow x N
  /-- The comparison of restrictions is an isomorphism. -/
  restrictIso_isIso : IsIso restrictIso
  /-- The comparison of restrictions lies over `Spec.map isoN`. -/
  restrictIso_isHomLift :
    X.p.IsHomLift (isoNOverHom x toS maximalIdeal N isoN isoN_over) restrictIso
  /-- Isomorphism of associated graded rings of the two maximal ideals. -/
  grIso :
    Ideal.AssociatedGraded.ring (IsLocalRing.maximalIdeal x.base.carrier) ≃+*
      Ideal.AssociatedGraded.ring maximalIdeal
  /-- `grIso` identifies homogeneous pieces of each degree. -/
  grIso_mem_grade :
    ∀ (n : ℕ) (y : Ideal.AssociatedGraded.ring (IsLocalRing.maximalIdeal x.base.carrier)),
      y ∈ Ideal.AssociatedGraded.grade (IsLocalRing.maximalIdeal x.base.carrier) n ↔
        grIso y ∈ Ideal.AssociatedGraded.grade maximalIdeal n
  /-- `grIso` is linear over the residue identification induced by `isoN`. -/
  grIso_residue :
    ∀ (hN : 1 ≤ N) (r : x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier),
      algebraMap (carrier ⧸ maximalIdeal) (Ideal.AssociatedGraded.ring maximalIdeal)
          (residueIsoOf x maximalIdeal N isoN isoN_map_maximal hN r) =
        grIso
          (algebraMap (x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier)
            (Ideal.AssociatedGraded.ring (IsLocalRing.maximalIdeal x.base.carrier)) r)

namespace ArtinApproximation

variable {X : GroupoidsOver S} {x : CompleteLocalObject X} {N : ℕ}

/-- Package Artin approximation data of a complete local object at order `N`. -/
def of (carrier : Type u) [CommRing carrier]
    (toS : Spec (CommRingCat.of carrier) ⟶ S) (finiteType : Scheme.Hom.FiniteType toS)
    (mA : Ideal carrier) (isMaximal : mA.IsMaximal) (object : X.total)
    (over_obj : X.p.obj object = Over.mk toS)
    (isoN :
      x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier ^ N ≃+* carrier ⧸ mA ^ N)
    (isoN_over :
      Spec.map (CommRingCat.ofHom isoN.toRingHom) ≫ x.base.powToS N =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ toS)
    (isoN_map_maximal :
      Ideal.map (Ideal.Quotient.mk (mA ^ N)) mA =
        Ideal.map isoN.toRingHom
          (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal x.base.carrier ^ N))
            (IsLocalRing.maximalIdeal x.base.carrier)))
    (restrictIso :
      IsPreFibered.pullbackObj over_obj (powOverHomOf toS mA N) ⟶
            GroupoidsOver.restrictionPow x N)
    (restrictIso_isIso : IsIso restrictIso)
    (restrictIso_isHomLift :
      X.p.IsHomLift (isoNOverHom x toS mA N isoN isoN_over) restrictIso)
    (grIso :
      Ideal.AssociatedGraded.ring (IsLocalRing.maximalIdeal x.base.carrier) ≃+*
        Ideal.AssociatedGraded.ring mA)
    (grIso_mem_grade :
      ∀ (n : ℕ) (y : Ideal.AssociatedGraded.ring (IsLocalRing.maximalIdeal x.base.carrier)),
        y ∈ Ideal.AssociatedGraded.grade (IsLocalRing.maximalIdeal x.base.carrier) n ↔
          grIso y ∈ Ideal.AssociatedGraded.grade mA n)
    (grIso_residue :
      ∀ (hN : 1 ≤ N) (r : x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier),
        algebraMap (carrier ⧸ mA) (Ideal.AssociatedGraded.ring mA)
            (residueIsoOf x mA N isoN isoN_map_maximal hN r) =
          grIso
            (algebraMap (x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier)
              (Ideal.AssociatedGraded.ring (IsLocalRing.maximalIdeal x.base.carrier)) r)) :
    ArtinApproximation x N where
  carrier := CommRingCat.of carrier
  toS := toS
  finiteType := finiteType
  maximalIdeal := mA
  isMaximal := isMaximal
  object := object
  over_obj := over_obj
  isoN := isoN
  isoN_over := isoN_over
  isoN_map_maximal := isoN_map_maximal
  restrictIso := restrictIso
  restrictIso_isIso := restrictIso_isIso
  restrictIso_isHomLift := restrictIso_isHomLift
  grIso := grIso
  grIso_mem_grade := grIso_mem_grade
  grIso_residue := grIso_residue

/-- Spectrum of the order-`N` truncation of the approximating algebra. -/
def powSpec (A : ArtinApproximation x N) : Scheme.{u} :=
  Spec (.of (A.carrier ⧸ A.maximalIdeal ^ N))

/-- `powSpec` is the spectrum of the order-`N` quotient of the approximating
algebra. -/
theorem powSpec_eq (A : ArtinApproximation x N) :
    A.powSpec = Spec (.of (A.carrier ⧸ A.maximalIdeal ^ N)) :=
  sorry

/-- Structure morphism `Spec(A ⧸ m_A ^ N) ⟶ S` of the approximating truncation. -/
def powToS (A : ArtinApproximation x N) : A.powSpec ⟶ S :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (A.maximalIdeal ^ N))) ≫ A.toS

/-- Restriction morphism `Spec(A ⧸ m_A ^ N) ⟶ Spec(A)` in `Over S`. -/
def powOverHom (A : ArtinApproximation x N) :
    Over.mk A.powToS ⟶ Over.mk A.toS :=
  powOverHomOf A.toS A.maximalIdeal N

/-- The underlying scheme morphism of `powOverHom` is the spectrum of the
order-`N` quotient map. -/
theorem powOverHom_left (A : ArtinApproximation x N) :
    A.powOverHom.left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (A.maximalIdeal ^ N))) :=
  sorry

/-- Restriction of the approximating object along `Spec(A ⧸ m_A ^ N) ⟶ Spec(A)`. -/
def restrictionPow (A : ArtinApproximation x N) : X.total :=
  IsPreFibered.pullbackObj A.over_obj A.powOverHom

/-- The approximating object restricted to `Spec(A ⧸ m_A ^ N)` lies over that
truncation. -/
theorem restrictionPow_over (A : ArtinApproximation x N) :
    X.p.obj A.restrictionPow = Over.mk A.powToS :=
  sorry

/-- Residue identification `R ⧸ m_R ≃+* A ⧸ m_A` induced by `isoN` when `1 ≤ N`. -/
def residueIso (A : ArtinApproximation x N) (hN : 1 ≤ N) :
    x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier ≃+*
      A.carrier ⧸ A.maximalIdeal :=
  residueIsoOf x A.maximalIdeal N A.isoN A.isoN_map_maximal hN

/-- The residue identification of approximation data is the identification induced
by `isoN`. -/
theorem residueIso_eq (A : ArtinApproximation x N) (hN : 1 ≤ N) :
    A.residueIso hN = residueIsoOf x A.maximalIdeal N A.isoN A.isoN_map_maximal hN :=
  sorry

/-- Artin approximation data specify a finite type structure
morphism, maximal ideal, object over `Spec(A)`, `S`-isomorphism of truncations,
compatible restriction isomorphism, and graded residue-algebra isomorphism. -/
theorem spec (A : ArtinApproximation x N) :
    Scheme.Hom.FiniteType A.toS ∧
      A.maximalIdeal.IsMaximal ∧
        X.p.obj A.object = Over.mk A.toS ∧
          (Spec.map (CommRingCat.ofHom A.isoN.toRingHom) ≫ x.base.powToS N =
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (A.maximalIdeal ^ N))) ≫
              A.toS) ∧
            IsIso A.restrictIso ∧
              X.p.IsHomLift (isoNOverHom x A.toS A.maximalIdeal N A.isoN A.isoN_over)
                  A.restrictIso ∧
                (∀ (n : ℕ)
                    (y : Ideal.AssociatedGraded.ring
                      (IsLocalRing.maximalIdeal x.base.carrier)),
                    y ∈ Ideal.AssociatedGraded.grade
                        (IsLocalRing.maximalIdeal x.base.carrier) n ↔
                      A.grIso y ∈ Ideal.AssociatedGraded.grade A.maximalIdeal n) ∧
                  ∀ (hN : 1 ≤ N)
                    (r : x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier),
                    algebraMap (A.carrier ⧸ A.maximalIdeal)
                        (Ideal.AssociatedGraded.ring A.maximalIdeal)
                        (residueIsoOf x A.maximalIdeal N A.isoN A.isoN_map_maximal hN r) =
                      A.grIso
                        (algebraMap
                          (x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier)
                          (Ideal.AssociatedGraded.ring
                            (IsLocalRing.maximalIdeal x.base.carrier))
                          r) :=
  sorry

/-- Existence of Artin approximation data is equivalent to the existence of a
finite type `S`-algebra, a maximal ideal, an object over `Spec(A)`, an
`S`-isomorphism of `N`-truncations, a compatible restriction isomorphism, and a
graded residue-algebra isomorphism. -/
theorem nonempty_iff :
    Nonempty (ArtinApproximation x N) ↔
      ∃ (A : Type u) (_ : CommRing A) (toS : Spec (CommRingCat.of A) ⟶ S)
        (_ : Scheme.Hom.FiniteType toS) (mA : Ideal A) (_ : mA.IsMaximal) (xA : X.total)
        (over_obj : X.p.obj xA = Over.mk toS)
        (isoN :
          x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier ^ N ≃+* A ⧸ mA ^ N)
        (isoN_over :
          Spec.map (CommRingCat.ofHom isoN.toRingHom) ≫ x.base.powToS N =
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ toS)
        (isoN_map_maximal :
          Ideal.map (Ideal.Quotient.mk (mA ^ N)) mA =
            Ideal.map isoN.toRingHom
              (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal x.base.carrier ^ N))
                (IsLocalRing.maximalIdeal x.base.carrier)))
        (restrictIso :
          IsPreFibered.pullbackObj over_obj (powOverHomOf toS mA N) ⟶
            GroupoidsOver.restrictionPow x N)
        (_ : IsIso restrictIso)
        (_ : X.p.IsHomLift (isoNOverHom x toS mA N isoN isoN_over) restrictIso)
        (grIso :
          Ideal.AssociatedGraded.ring (IsLocalRing.maximalIdeal x.base.carrier) ≃+*
            Ideal.AssociatedGraded.ring mA),
        (∀ (n : ℕ) (y : Ideal.AssociatedGraded.ring (IsLocalRing.maximalIdeal x.base.carrier)),
            y ∈ Ideal.AssociatedGraded.grade (IsLocalRing.maximalIdeal x.base.carrier) n ↔
              grIso y ∈ Ideal.AssociatedGraded.grade mA n) ∧
          ∀ (hN : 1 ≤ N) (r : x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier),
            algebraMap (A ⧸ mA) (Ideal.AssociatedGraded.ring mA)
                (residueIsoOf x mA N isoN isoN_map_maximal hN r) =
              grIso
                (algebraMap (x.base.carrier ⧸ IsLocalRing.maximalIdeal x.base.carrier)
                  (Ideal.AssociatedGraded.ring (IsLocalRing.maximalIdeal x.base.carrier)) r) :=
  sorry

end ArtinApproximation

end AlgebraicGeometry.GroupoidsOver
