/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Definition_61_29_4_Completion
public import stacks_project.Chap61.Definition_61_29_4_Pullback
public import stacks_project.Chap61.Definition_61_29_4_Lisse
public import stacks_project.Chap61.Definition_61_29_4_Constructible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.ProEt

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
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
variable (I : Ideal Λ) (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ)))

/- Definition 61.29.4 (1): an object `K` of `D(X_proétale, Λ)` is adic lisse when there exists
a finite complex of finite projective `Λ^∧`-modules whose completed constant complex, with
constant differentials, is locally isomorphic to `K`. -/
@[stacks 09C4] #check
  (AlgebraicGeometry.Scheme.ProEt.Derived.IsAdicLisse (I := I) (K := K) : Prop)

/- Definition 61.29.4 (2): an object `K` of `D(X_proétale, Λ)` is adic constructible when every
affine open of `X` admits a decomposition into constructible locally closed subschemes on which
the restriction of `K` is adic lisse. -/
@[stacks 09C4] #check
  (AlgebraicGeometry.Scheme.ProEt.Derived.IsAdicConstructible (I := I) (K := K) : Prop)
