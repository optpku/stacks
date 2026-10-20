module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleTorFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Etale.FrobeniusStalk
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Derived.FiniteRing

section FiniteCoefficients

variable {X : Scheme.{u}} {Λ : Type u} [Ring Λ] [Finite Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
    (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- A cochain complex of étale modules is bounded constructible with projective
geometric stalks if it is supported in a finite integer interval, its terms are
constructible, and their stalks at every separably closed field-valued point are projective. -/
def constructibleProjectiveStalkComplex
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ) : Prop :=
  (∃ a b : ℤ, a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
    (∀ i : ℤ, Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) (P.X i)) ∧
    (∀ (i : ℤ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ X),
      Module.Projective Λ
        (((Scheme.pointSmallEtale s).sheafFiber :
          Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ).obj (P.X i)))

/-- A derived étale module object admits a bounded constructible complex with
projective geometric stalks. On quasi-compact quasi-separated schemes over a
finite ring this is the constructible Tor-finite property. -/
def constructibleTorFinite :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  fun K ↦ ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ,
    Nonempty (DerivedCategory.Q.obj P ≅ K) ∧ constructibleProjectiveStalkComplex P

/-- The full subcategory of derived objects admitting bounded constructible
representatives with projective geometric stalks; on quasi-compact quasi-separated
schemes over finite rings it is the constructible Tor-finite derived category. -/
abbrev ConstructibleTorFinite := (constructibleTorFinite (X := X) (Λ := Λ)).FullSubcategory

/-- Membership is equivalent to existence of a bounded constructible representative
with projective geometric stalks. -/
theorem constructibleTorFinite_iff
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    constructibleTorFinite K ↔
      ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ,
        Nonempty (DerivedCategory.Q.obj P ≅ K) ∧ constructibleProjectiveStalkComplex P := Iff.rfl

end FiniteCoefficients

section CommutativeCoefficients

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ] [Finite Λ] [IsNoetherianRing Λ]
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale, Abelian (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ U : X.Etale,
  HasDerivedCategory (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ))]
variable [∀ U : X.Etale, ((X.smallEtaleTopology.over U).W (A := ModuleCat.{u} Λ)).IsMonoidal]

/-- Over a finite commutative Noetherian ring on a quasi-compact quasi-separated
scheme, the projective-stalk representative criterion agrees with constructible
cohomology and covering-local finite Tor dimension. -/
theorem constructibleTorFinite_iff_of_commRing
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    constructibleTorFinite K ↔
      AlgebraicGeometry.Scheme.Etale.Derived.constructibleTorFinite X Λ K := sorry

end CommutativeCoefficients

end AlgebraicGeometry.Scheme.Etale.Derived.FiniteRing

end
