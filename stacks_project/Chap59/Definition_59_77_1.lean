/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_76_1
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleTorFinite
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

@[expose] public section

universe u v

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]

/-- The unbounded derived category of sheaves of `Λ`-modules on the small étale site of `X`. -/
abbrev EtaleDerived (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))] :=
  DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))

section canonical_check

variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ U : X.Etale, Abelian (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale,
  HasDerivedCategory (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale, ((X.smallEtaleTopology.over U).W (A := ModuleCat.{v} Λ)).IsMonoidal]

/- Definition 59.77.1: for a scheme `X` and a Noetherian ring `Λ`, `D_ctf(Xₑₜ, Λ)` is
the full subcategory of `D_c(Xₑₜ, Λ)` consisting of objects with locally finite Tor dimension. -/
@[stacks 03TQ] #check
  (AlgebraicGeometry.Scheme.Etale.Derived.ConstructibleTorFinite X Λ :
    Type (max (u + 1) (v + 1)))

end canonical_check

end AlgebraicGeometry.Scheme
