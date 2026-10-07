module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.SetTheory.Cardinal.NatCard
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.RingTheory.Henselian.StrictHenselian

/-!
# Locally finite type étale slice with constant finite coefficients

The full subcategory of schemes locally of finite type over a base `S`, equipped with the
restricted étale topology and the constant sheaf of a finite ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Schemes locally of finite type over a fixed base, as objects of `(Sch/S)_étale`. -/
abbrev locallyOfFiniteTypeOver (S : Scheme.{u}) :=
  MorphismProperty.Over (@LocallyOfFiniteType) ⊤ S

/-- The structure morphism of an object of `locallyOfFiniteTypeOver S` is locally of finite type. -/
instance instLocallyOfFiniteType_hom {S : Scheme.{u}} (V : locallyOfFiniteTypeOver S) :
    LocallyOfFiniteType V.hom :=
  V.prop

/-- The étale topology on schemes locally of finite type over `S`, obtained by restricting the
big étale topology on `Over S`. -/
def etaleTopology (S : Scheme.{u}) :
    GrothendieckTopology (locallyOfFiniteTypeOver S) :=
  (MorphismProperty.Over.forget (@LocallyOfFiniteType) ⊤ S).restrictedTopology
    (S.overGrothendieckTopology @Etale)

/-- The constant sheaf of rings `Λ` on the locally finite type étale slice of `S`. -/
def constantRingSheaf (S : Scheme.{u}) (Λ : Type u) [Ring Λ]
    [HasWeakSheafify (etaleTopology S) RingCat.{u}] :
    Sheaf (etaleTopology S) RingCat.{u} :=
  (constantSheaf (etaleTopology S) RingCat.{u}).obj (RingCat.of Λ)

/-- The ringed site given by the locally finite type étale slice of `S` with constant
coefficients `Λ`. -/
def ringedSite (S : Scheme.{u}) (Λ : Type u) [Ring Λ]
    [HasWeakSheafify (etaleTopology S) RingCat.{u}] :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (etaleTopology S) (constantRingSheaf S Λ)

/-- Étale sheaves of `Λ`-modules on the locally finite type slice of `S`. -/
abbrev modules (S : Scheme.{u}) (Λ : Type u) [Ring Λ]
    [HasWeakSheafify (etaleTopology S) RingCat.{u}] :=
  SheafOfModules.{u} (constantRingSheaf S Λ)

/-- The order of a finite coefficient ring `Λ` is invertible on `S`. -/
def orderInvertible (S : Scheme.{u}) (Λ : Type u) [Ring Λ] [Finite Λ] : Prop :=
  IsUnit (Nat.card Λ : Γ(S, ⊤))

/-- Invertibility of the order of `Λ` on `S` is invertibility of `Nat.card Λ` in `Γ(S, ⊤)`. -/
theorem orderInvertible_iff (S : Scheme.{u}) (Λ : Type u) [Ring Λ] [Finite Λ] :
    orderInvertible S Λ ↔ IsUnit (Nat.card Λ : Γ(S, ⊤)) :=
  sorry

/-- Allowed bases for the finite-coefficient étale unbounded-descent example: spectra of a finite
field, a separably closed field, a strictly henselian Noetherian local ring, or a henselian
Noetherian local ring with finite residue field. -/
inductive IsFiniteEtaleCoefficientBase (S : Scheme.{u}) : Prop where
  /-- The spectrum of a finite field. -/
  | ofFiniteField [IsAffine S] [Field Γ(S, ⊤)] [Finite Γ(S, ⊤)]
  /-- The spectrum of a separably closed field. -/
  | ofSeparablyClosed [IsAffine S] [Field Γ(S, ⊤)] [IsSepClosed Γ(S, ⊤)]
  /-- The spectrum of a strictly henselian Noetherian local ring. -/
  | ofStrictlyHenselian [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
      [StrictHenselianLocalRing Γ(S, ⊤)]
  /-- The spectrum of a henselian Noetherian local ring with finite residue field. -/
  | ofHenselianFiniteResidue [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
      [HenselianLocalRing Γ(S, ⊤)] [Finite (IsLocalRing.ResidueField Γ(S, ⊤))]

/-- An allowed finite-coefficient étale base is affine. -/
theorem IsFiniteEtaleCoefficientBase.isAffine {S : Scheme.{u}}
    (hS : IsFiniteEtaleCoefficientBase S) : IsAffine S :=
  sorry

/-- All étale sheaves of `Λ`-modules form a weak Serre class. -/
instance instIsWeakSerreClass_modules (S : Scheme.{u}) (Λ : Type u) [Ring Λ]
    [HasWeakSheafify (etaleTopology S) RingCat.{u}]
    [HasSheafify (etaleTopology S) AddCommGrpCat.{u}]
    [(etaleTopology S).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ObjectProperty.IsWeakSerreClass (⊤ : ObjectProperty (modules S Λ)) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
