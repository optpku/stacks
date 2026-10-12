/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.Constructible
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.AlgebraicGeometry.Scheme.LocallyClosedReduction
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DerivedCompletion
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DerivedRestriction
public import ReasLib.Topology.Stratification.Partition

/-!
# Derived adic lisse and constructible objects

This file defines the local derived-isomorphism, adic lisse, and adic
constructible predicates for complexes of sheaves on the small pro-étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

namespace Derived

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]
variable [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [∀ U : X.ProEt, Abelian (Sheaf ((topology X).over U) (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [∀ U : X.ProEt, HasDerivedCategory (Sheaf ((topology X).over U) (ModuleCat.{w} Λ))]
variable [∀ U : X.ProEt, ((topology X).overPullback (ModuleCat.{w} Λ) U).Additive]
variable [∀ U : X.ProEt, PreservesFiniteLimits ((topology X).overPullback (ModuleCat.{w} Λ) U)]
variable [∀ U : X.ProEt, PreservesFiniteColimits ((topology X).overPullback (ModuleCat.{w} Λ) U)]
variable [HasTerminal X.ProEt]

/-- Derived restriction of an object to the slice site over a pro-étale object. -/
abbrev derivedSlice
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) (U : X.ProEt) :
    DerivedCategory (Sheaf ((topology X).over U) (ModuleCat.{w} Λ)) :=
  ((topology X).overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory.obj K

/-- `derivedSlice` is slicewise derived restriction. -/
theorem derivedSlice_obj
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) (U : X.ProEt) :
    derivedSlice K U =
      ((topology X).overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory.obj K :=
  sorry

/-- Two derived objects are locally isomorphic when a cover of the terminal object
has slicewise derived isomorphisms. -/
class IsLocallyIsomorphic
    (K L : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) : Prop where
  /-- A cover of the terminal object has slicewise derived isomorphisms. -/
  existsCover :
    ∃ T : (topology X).Cover (⊤_ X.ProEt),
      ∀ i : T.Arrow, Nonempty (derivedSlice K i.Y ≅ derivedSlice L i.Y)

/-- Unfolding `IsLocallyIsomorphic` gives the covering-by-slice-isos criterion. -/
theorem isLocallyIsomorphic_iff
    (K L : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) :
    IsLocallyIsomorphic K L ↔
      ∃ T : (topology X).Cover (⊤_ X.ProEt),
        ∀ i : T.Arrow, Nonempty (derivedSlice K i.Y ≅ derivedSlice L i.Y) :=
  sorry

/-- Local isomorphism of derived objects is reflexive. -/
instance instIsLocallyIsomorphic_self
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) :
    IsLocallyIsomorphic K K :=
  sorry

/-- Local isomorphism is invariant under replacing the first object by an isomorphic object. -/
theorem isLocallyIsomorphic_of_iso
    {K K' L : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))}
    (e : K ≅ K') (h : IsLocallyIsomorphic K L) : IsLocallyIsomorphic K' L :=
  sorry

variable (I : Ideal Λ)

/-- The completed-constant functor preserves zero morphisms in the derived setting. -/
instance constantAdicCompletionFunctor_preservesZeroMorphisms_preadditive :
    (constantAdicCompletionFunctor (topology X) I).PreservesZeroMorphisms :=
  sorry

/-- The derived object represented by a completed constant complex. -/
def ofConstantAdicCompletionComplex
    (M : CochainComplex (ModuleCat.{w} (AdicCompletion I Λ)) ℤ) :
    DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ)) :=
  DerivedCategory.Q.obj
    (((constantAdicCompletionFunctor (topology X) I).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)

/-- `ofConstantAdicCompletionComplex` is `Q` of the completed constant complex. -/
theorem ofConstantAdicCompletionComplex_obj
    (M : CochainComplex (ModuleCat.{w} (AdicCompletion I Λ)) ℤ) :
    ofConstantAdicCompletionComplex I M =
      DerivedCategory.Q.obj
        (((constantAdicCompletionFunctor (topology X) I).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) :=
  sorry

/-- An object is adic lisse when it is locally isomorphic to a completed constant
complex of finite projective `Λ^∧`-modules. -/
class IsAdicLisse [IsNoetherianRing Λ]
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) : Prop where
  /-- A bounded finite projective completed constant complex models `K` locally. -/
  existsModel :
    ∃ M : CochainComplex (ModuleCat.{w} (AdicCompletion I Λ)) ℤ,
      M.IsBoundedFiniteProjective ∧
        IsLocallyIsomorphic K (ofConstantAdicCompletionComplex I M)

section Lisse

variable [IsNoetherianRing Λ]

/-- Adic lisseness is the existence of a bounded finite projective model. -/
theorem isAdicLisse_iff
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) :
    IsAdicLisse I K ↔
      ∃ M : CochainComplex (ModuleCat.{w} (AdicCompletion I Λ)) ℤ,
        M.IsBoundedFiniteProjective ∧
          IsLocallyIsomorphic K (ofConstantAdicCompletionComplex I M) :=
  sorry

/-- The defining conditions of an adic lisse derived object. -/
theorem IsAdicLisse.spec
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ)))
    [IsAdicLisse I K] :
    ∃ M : CochainComplex (ModuleCat.{w} (AdicCompletion I Λ)) ℤ,
      M.IsBoundedFiniteProjective ∧
        IsLocallyIsomorphic K (ofConstantAdicCompletionComplex I M) :=
  sorry

/-- Adic lisseness is invariant under derived isomorphism. -/
theorem isAdicLisse_of_iso
    {K L : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))}
    (e : K ≅ L) [IsAdicLisse I K] : IsAdicLisse I L :=
  sorry

/-- A completed constant finite-projective complex is adic lisse. -/
instance instIsAdicLisse_constantAdicCompletionComplex
    (M : CochainComplex (ModuleCat.{w} (AdicCompletion I Λ)) ℤ)
    [M.IsBoundedFiniteProjective] :
    IsAdicLisse I
      (ofConstantAdicCompletionComplex I M :
        DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) :=
  sorry

end Lisse

variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((topology Y).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf (topology Y) (ModuleCat.{w} Λ))]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  Abelian (Sheaf ((topology Y).over U) (ModuleCat.{w} Λ))]
variable [∀ {Y : Scheme.{u}}, HasDerivedCategory (Sheaf (topology Y) (ModuleCat.{w} Λ))]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasDerivedCategory (Sheaf ((topology Y).over U) (ModuleCat.{w} Λ))]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  ((topology Y).overPullback (ModuleCat.{w} Λ) U).Additive]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  PreservesFiniteLimits ((topology Y).overPullback (ModuleCat.{w} Λ) U)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  PreservesFiniteColimits ((topology Y).overPullback (ModuleCat.{w} Λ) U)]
variable [∀ {Y : Scheme.{u}}, HasTerminal Y.ProEt]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
  (baseChange f).op.HasLeftKanExtension P]

/-- An object is adic constructible when affine opens admit finite constructible
locally closed strata on which the derived restriction is adic lisse. -/
class IsAdicConstructible [IsNoetherianRing Λ]
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) : Prop where
  /-- Affine opens admit constructible locally closed strata with adic lisse restrictions. -/
  existsAffineStrata :
    ∀ (U : X.Opens), IsAffineOpen U →
      ∃ Q : LocallyClosedPartition U.toScheme, Q.toSet.Finite ∧
        ∀ s : Q.toSet,
          Topology.IsConstructible (s : Set U.toScheme) ∧
            let T : LocallyCloseds U.toScheme :=
              ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
            IsAdicLisse I
              ((restrictDerived (LocallyClosedReduction.ι T ≫ U.ι)).obj K)

variable [IsNoetherianRing Λ]

/-- Unfolding `IsAdicConstructible` gives the affine finite-stratification criterion. -/
theorem isAdicConstructible_iff
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) :
    IsAdicConstructible I K ↔
      ∀ (U : X.Opens), IsAffineOpen U →
        ∃ Q : LocallyClosedPartition U.toScheme, Q.toSet.Finite ∧
          ∀ s : Q.toSet,
            Topology.IsConstructible (s : Set U.toScheme) ∧
              let T : LocallyCloseds U.toScheme :=
                ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
              IsAdicLisse I
                ((restrictDerived (LocallyClosedReduction.ι T ≫ U.ι)).obj K) :=
  sorry

/-- The defining affine-stratum conditions of an adic constructible derived object. -/
theorem IsAdicConstructible.spec
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ)))
    [IsAdicConstructible I K] :
    ∀ (U : X.Opens), IsAffineOpen U →
      ∃ Q : LocallyClosedPartition U.toScheme, Q.toSet.Finite ∧
        ∀ s : Q.toSet,
          Topology.IsConstructible (s : Set U.toScheme) ∧
            let T : LocallyCloseds U.toScheme :=
              ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
            IsAdicLisse I
              ((restrictDerived (LocallyClosedReduction.ι T ≫ U.ι)).obj K) :=
  sorry

/-- An adic lisse derived object is adic constructible. -/
instance instIsAdicConstructible_of_isAdicLisse
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ)))
    [IsAdicLisse I K] : IsAdicConstructible I K :=
  sorry

end Derived

end AlgebraicGeometry.Scheme.ProEt
