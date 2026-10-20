/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import Mathlib.CategoryTheory.CommSq

/-!
# Base change for relative differentials on a ringed site

A commutative square of commutative ring sheaves induces a canonical morphism on relative
differentials.  The construction is carried out on the sectionwise Kahler-differential
presheaves and then descended through the universal derivation.
-/

@[expose] public section

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped RelativeDerivation SheafOfModules.RingedSite

noncomputable section

universe c v w

namespace SheafOfModules.RingedSite.RelativeDifferentials

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{w}}
variable {a : O₁ ⟶ O₁'} {phi : O₁ ⟶ O₂}
variable {phi' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}

/-- The sectionwise commutativity relation underlying a square of commutative ring sheaves. -/
theorem squareApp (sq : CommSq a phi phi' b) (X : Cᵒᵖ) :
    a.hom.app X ≫ phi'.hom.app X = phi.hom.app X ≫ b.hom.app X := sorry

/-- Restriction of module presheaves along the lower edge of a square of ring sheaves. -/
abbrev presheafRestriction (b : O₂ ⟶ O₂') :=
  PresheafOfModules.restrictScalars (ringSheafMap b).hom

/-- The sectionwise map on Kahler differentials induced by a commutative ring square. -/
abbrev mapApp (sq : CommSq a phi phi' b) (X : Cᵒᵖ) :
    (relativeDifferentials' phi.hom).obj X ⟶
      ((presheafRestriction b).obj (relativeDifferentials' phi'.hom)).obj X :=
  CommRingCat.KaehlerDifferential.map (squareApp sq X)

/-- The sectionwise maps on Kahler differentials commute with restriction in the site. -/
theorem mapApp_naturality (sq : CommSq a phi phi' b) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (relativeDifferentials' phi.hom).map f ≫
        (ModuleCat.restrictScalars (((ringSheaf J O₂).obj.map f).hom)).map
          (mapApp sq Y) =
      mapApp sq X ≫
        ((presheafRestriction b).obj (relativeDifferentials' phi'.hom)).map f := sorry

/-- The comparison of sectionwise relative-differentials presheaves induced by a ring square. -/
noncomputable def presheafMap (sq : CommSq a phi phi' b) :
    relativeDifferentials' phi.hom ⟶
      (presheafRestriction b).obj (relativeDifferentials' phi'.hom) where
  app X := mapApp sq X
  naturality f := mapApp_naturality sq f

/-- The target `phi`-derivation obtained from the comparison of relative-differentials
presheaves and the target sheafification unit. -/
abbrev mapDerivation (sq : CommSq a phi phi' b) :
    Der[phi ; (restrictionAlong b).obj (relativeDifferentials phi')] :=
  (derivation' phi.hom).postcomp
    (presheafMap sq ≫
      (presheafRestriction b).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringSheaf J O₂').obj)).unit.app (relativeDifferentials' phi'.hom)))

/-- A commutative square of commutative ring sheaves induces the canonical map on relative
differentials. -/
@[stacks 08RS, stacks 08TR]
noncomputable def map (sq : CommSq a phi phi' b) :
    relativeDifferentials phi ⟶
      (restrictionAlong b).obj (relativeDifferentials phi') :=
  relativeDifferentialDesc phi (mapDerivation sq)

/-- The map on relative differentials factors the universal derivation through the derivation
induced by the commutative ring square. -/
theorem map_fac (sq : CommSq a phi phi' b) :
    (relativeDifferential phi).postcomp (map sq).val = mapDerivation sq := sorry

/-- The canonical map on relative differentials sends `d f` to `d (b f)` on every object of
the site. -/
@[simp]
theorem map_d (sq : CommSq a phi phi' b) (X : Cᵒᵖ) (f : O₂.obj.obj X) :
    (map sq).val.app X (((relativeDifferential phi).app X).d f) =
      ((relativeDifferential phi').app X).d (b.hom.app X f) := sorry

/-- A morphism on relative differentials is the canonical base-change map when it has the
expected value on all universal differential generators. -/
theorem map_unique (sq : CommSq a phi phi' b)
    (f : relativeDifferentials phi ⟶
      (restrictionAlong b).obj (relativeDifferentials phi'))
    (hf : ∀ (X : Cᵒᵖ) (x : O₂.obj.obj X),
      f.val.app X (((relativeDifferential phi).app X).d x) =
        ((relativeDifferential phi').app X).d (b.hom.app X x)) :
    f = map sq := sorry

/-- Canonical maps on relative differentials are compatible with horizontal composition of
commutative ring squares. -/
theorem map_comp
    {O₁'' O₂'' : Sheaf J CommRingCat.{w}}
    {a' : O₁' ⟶ O₁''} {phi'' : O₁'' ⟶ O₂''} {b' : O₂' ⟶ O₂''}
    (sq : CommSq a phi phi' b) (sq' : CommSq a' phi' phi'' b') :
    map (CommSq.horiz_comp sq sq') =
      map sq ≫ (restrictionAlong b).map (map sq') := sorry

/-- The identity square on a morphism of commutative ring sheaves. -/
@[stacks 08RS "identity square for relative differentials"]
theorem idSquare (φ : O₁ ⟶ O₂) :
    CommSq (𝟙 O₁) φ φ (𝟙 O₂) := sorry

/-- The map attached to an identity square is the canonical identity-restriction comparison. -/
@[simp, stacks 08RS "identity law for relative differentials"]
theorem map_id (φ : O₁ ⟶ O₂) :
    map (idSquare φ) =
      (SheafOfModules.Restriction.idIso (ringSheaf J O₂)).hom.app
        (relativeDifferentials φ) := sorry

/-- Composition of base-change maps with the restriction coherence made explicit.  The shorter
`map_comp` theorem remains available for clients whose ambient restriction maps are definitionally
identified. -/
@[stacks 08RS "coherent composition law for relative differentials"]
theorem map_comp_coherent
    {O₁'' O₂'' : Sheaf J CommRingCat.{w}}
    {a' : O₁' ⟶ O₁''} {phi'' : O₁'' ⟶ O₂''} {b' : O₂' ⟶ O₂''}
    (sq : CommSq a phi phi' b) (sq' : CommSq a' phi' phi'' b') :
    map (CommSq.horiz_comp sq sq') =
      map sq ≫ (restrictionAlong b).map (map sq') ≫
        (SheafOfModules.Restriction.compIso (ringSheafMap b) (ringSheafMap b')).hom.app
          (relativeDifferentials phi'') := sorry

end SheafOfModules.RingedSite.RelativeDifferentials
