/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials

/-!
# Relative differentials on topological spaces

This file is the stable geometric import path for relative differentials.  The actual construction
and universal property live at the site-generic layer in
`SheafOfModules.RingedSite`; the declarations below specialize that API to the opens site of a
topological space.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open AlgebraicGeometry
open PresheafOfModules.DifferentialsConstruction
open scoped RelativeDerivation

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {O₁ O₂ : X.Sheaf CommRingCat.{u}}

/-- The opens-site view of the site-generic relative-differentials sheaf. -/
@[stacks 08RP "opens-site specialization"]
abbrev relativeDifferentials (φ : O₁ ⟶ O₂) : SheafOfModules (ringSheafOfComm O₂) :=
  SheafOfModules.RingedSite.relativeDifferentials
    (J := Opens.grothendieckTopology X) φ

/-- The opens-site view of the universal relative derivation. -/
@[stacks 08RP "opens-site universal derivation"]
abbrev relativeDifferential (φ : O₁ ⟶ O₂) :
    SheafOfModules.RelativeDerivation
      (J := Opens.grothendieckTopology X) φ (relativeDifferentials φ) :=
  SheafOfModules.RingedSite.relativeDifferential
    (J := Opens.grothendieckTopology X) φ

/-- The opens-site view of the morphism represented by a relative derivation. -/
@[stacks 08RM "opens-site desc"]
abbrev relativeDifferentialDesc (φ : O₁ ⟶ O₂)
    {F : SheafOfModules (ringSheafOfComm O₂)}
    (D : SheafOfModules.RelativeDerivation
      (J := Opens.grothendieckTopology X) φ F) :
    relativeDifferentials φ ⟶ F :=
  SheafOfModules.RingedSite.relativeDifferentialDesc
    (J := Opens.grothendieckTopology X) φ D

/-- The geometric relative-differentials view is the sheafification of the presheaf owner. -/
@[stacks 08TD "opens-site specialization"]
theorem relativeDifferentials_def (φ : O₁ ⟶ O₂) :
    relativeDifferentials φ =
      (PresheafOfModules.sheafification
        (𝟙 (ringSheafOfComm O₂).obj)).obj (relativeDifferentials' φ.hom) := sorry

/-- The represented morphism factors the given derivation through the universal derivation. -/
@[stacks 08RM "opens-site desc specification"]
theorem relativeDifferentialDesc_fac (φ : O₁ ⟶ O₂)
    {F : SheafOfModules (ringSheafOfComm O₂)}
    (D : SheafOfModules.RelativeDerivation
      (J := Opens.grothendieckTopology X) φ F) :
    (relativeDifferential φ).postcomp (relativeDifferentialDesc φ D).val = D := sorry

/-- A morphism out of `Ω(φ)` is determined by its composite with the universal derivation. -/
@[stacks 08RM "opens-site uniqueness"]
theorem relativeDifferential_postcomp_injective (φ : O₁ ⟶ O₂)
    {F : SheafOfModules (ringSheafOfComm O₂)}
    ⦃f g : relativeDifferentials φ ⟶ F⦄
    (h : (relativeDifferential φ).postcomp f.val =
      (relativeDifferential φ).postcomp g.val) :
    f = g := sorry

/-- The opens-site relative-differentials sheaf represents relative derivations. -/
@[stacks 08RM "opens-site specialization"]
theorem relativeDifferentials_representsDerivations (φ : O₁ ⟶ O₂)
    (F : SheafOfModules (ringSheafOfComm O₂))
    (D : SheafOfModules.RelativeDerivation
      (J := Opens.grothendieckTopology X) φ F) :
    ∃! f : relativeDifferentials φ ⟶ F,
      (relativeDifferential φ).postcomp f.val = D := sorry

namespace RelativeDifferentials

/-- The opens-site Hom--derivation equivalence for relative differentials. -/
@[stacks 08RM "opens-site Hom--derivation equivalence"]
noncomputable abbrev homEquiv (φ : O₁ ⟶ O₂)
    (F : SheafOfModules (ringSheafOfComm O₂)) :
    (relativeDifferentials φ ⟶ F) ≃
      SheafOfModules.RelativeDerivation
        (J := Opens.grothendieckTopology X) φ F :=
  SheafOfModules.RingedSite.RelativeDifferentials.homEquiv
    (J := Opens.grothendieckTopology X) φ F

/-- The opens-site relative-differentials sheaf corepresents relative derivations. -/
@[stacks 08RM "opens-site corepresented relative derivations"]
noncomputable abbrev corepresentableBy (φ : O₁ ⟶ O₂) :
    (SheafOfModules.RelativeDerivation.functor
      (J := Opens.grothendieckTopology X) φ).CorepresentableBy
        (relativeDifferentials φ) :=
  SheafOfModules.RingedSite.RelativeDifferentials.corepresentableBy
    (J := Opens.grothendieckTopology X) φ

/-- The opens-site natural representing isomorphism for relative differentials. -/
@[stacks 08RM "opens-site representing isomorphism"]
noncomputable abbrev representingIso (φ : O₁ ⟶ O₂) :
    coyoneda.obj (Opposite.op (relativeDifferentials φ)) ≅
      SheafOfModules.RelativeDerivation.functor
        (J := Opens.grothendieckTopology X) φ :=
  SheafOfModules.RingedSite.RelativeDifferentials.representingIso
    (J := Opens.grothendieckTopology X) φ

end RelativeDifferentials

end TopCat.Sheaf

@[inherit_doc TopCat.Sheaf.relativeDifferentials]
scoped[AlgebraicGeometry] notation:max "Ω(" φ ")" =>
  TopCat.Sheaf.relativeDifferentials φ
