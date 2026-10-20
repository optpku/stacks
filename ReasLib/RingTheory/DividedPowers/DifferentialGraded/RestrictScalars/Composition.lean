/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.RestrictScalars.Composition
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.RestrictScalars
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of restriction of scalars for divided-power chain DGAs

The canonical composition comparison for chain DGAs preserves the divided-power operations on
the positive even part.  It therefore lifts without changing any homogeneous function to an
isomorphism of divided-power chain DGAs.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uR uS uT uU uB

namespace DividedPowerChainAlgebra.RestrictScalars

section Map

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- The chain-DGA map underlying restriction of a divided-power morphism is the generic
restriction of its underlying chain-DGA map. -/
@[simp]
theorem map_toChainHom (sigma : R →+* S)
    {B C : DividedPowerChainAlgebra.{uS, uB} S} (phi : B ⟶ C) :
    (DividedPowerChainAlgebra.Hom.restrictScalars sigma phi).toChainHom =
      ChainDGAlgebra.RestrictScalars.map sigma phi.toChainHom := sorry

end Map

section Composition

variable {R : Type uR} {S : Type uS} {T : Type uT}
  [CommRing R] [CommRing S] [CommRing T]

/-- The chain-DGA composition isomorphism underlying successive restriction of a divided-power
chain DGA. -/
@[stacks 09PQ "underlying chain-DGA composition under restriction of scalars"]
def compChainIso (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    (DividedPowerChainAlgebra.restrictScalars (g.comp f) B).toChainDGAlgebra ≅
      (DividedPowerChainAlgebra.restrictScalars f
        (DividedPowerChainAlgebra.restrictScalars g B)).toChainDGAlgebra :=
  ChainDGAlgebra.RestrictScalars.compIso f g B.toChainDGAlgebra

/-- The chain-complex composition isomorphism underlying successive restriction of a
divided-power chain DGA. -/
@[stacks 09PQ "underlying chain-complex composition under restriction of scalars"]
def compComplexIso (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    (DividedPowerChainAlgebra.restrictScalars (g.comp f) B).toChainDGAlgebra.toChainComplex ≅
      (DividedPowerChainAlgebra.restrictScalars f
        (DividedPowerChainAlgebra.restrictScalars g B)).toChainDGAlgebra.toChainComplex :=
  ChainDGAlgebra.RestrictScalars.compComplexIso f g B.toChainDGAlgebra

/-- The forward underlying chain-DGA comparison is the generic restriction comparison. -/
@[simp]
theorem compChainIso_hom (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    (compChainIso f g B).hom =
      ChainDGAlgebra.RestrictScalars.compHom f g B.toChainDGAlgebra := sorry

/-- The inverse underlying chain-DGA comparison is the generic inverse restriction comparison. -/
@[simp]
theorem compChainIso_inv (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    (compChainIso f g B).inv =
      ChainDGAlgebra.RestrictScalars.compInv f g B.toChainDGAlgebra := sorry

/-- The forward underlying chain-complex comparison is the generic complex comparison. -/
@[simp]
theorem compComplexIso_hom (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    (compComplexIso f g B).hom =
      ChainDGAlgebra.RestrictScalars.compHomChainMap f g B.toChainDGAlgebra := sorry

/-- The inverse underlying chain-complex comparison is the generic inverse complex comparison. -/
@[simp]
theorem compComplexIso_inv (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    (compComplexIso f g B).inv =
      ChainDGAlgebra.RestrictScalars.compInvChainMap f g B.toChainDGAlgebra := sorry

/-- The generic forward composition comparison preserves the divided powers of the restricted
objects. -/
theorem compHom_map_gamma (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) (n : ℕ)
    (x : (DividedPowerChainAlgebra.restrictScalars (g.comp f) B).toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (ChainDGAlgebra.RestrictScalars.compHom f g B.toChainDGAlgebra).nonnegativePart.evenMap
        ((DividedPowerChainAlgebra.restrictScalars (g.comp f) B).gamma n x) =
      (DividedPowerChainAlgebra.restrictScalars f
          (DividedPowerChainAlgebra.restrictScalars g B)).gamma n
        ((ChainDGAlgebra.RestrictScalars.compHom f g B.toChainDGAlgebra).nonnegativePart.evenPositiveMap
          x) := sorry

/-- The generic inverse composition comparison preserves the divided powers of the restricted
objects. -/
theorem compInv_map_gamma (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) (n : ℕ)
    (x : (DividedPowerChainAlgebra.restrictScalars f
      (DividedPowerChainAlgebra.restrictScalars g B)).toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (ChainDGAlgebra.RestrictScalars.compInv f g B.toChainDGAlgebra).nonnegativePart.evenMap
        ((DividedPowerChainAlgebra.restrictScalars f
          (DividedPowerChainAlgebra.restrictScalars g B)).gamma n x) =
      (DividedPowerChainAlgebra.restrictScalars (g.comp f) B).gamma n
        ((ChainDGAlgebra.RestrictScalars.compInv f g B.toChainDGAlgebra).nonnegativePart.evenPositiveMap
          x) := sorry

/-- The forward divided-power morphism from direct restriction along a composite to successive
restriction. -/
@[stacks 09PQ "forward composition comparison for divided-power chain-DGA restriction"]
def compHom (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    DividedPowerChainAlgebra.Hom
      (DividedPowerChainAlgebra.restrictScalars (g.comp f) B)
      (DividedPowerChainAlgebra.restrictScalars f
        (DividedPowerChainAlgebra.restrictScalars g B)) where
  toChainHom := ChainDGAlgebra.RestrictScalars.compHom f g B.toChainDGAlgebra
  map_gamma := compHom_map_gamma f g B

/-- The inverse divided-power morphism from successive restriction back to direct restriction
along the composite. -/
@[stacks 09PQ "inverse composition comparison for divided-power chain-DGA restriction"]
def compInv (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    DividedPowerChainAlgebra.Hom
      (DividedPowerChainAlgebra.restrictScalars f
        (DividedPowerChainAlgebra.restrictScalars g B))
      (DividedPowerChainAlgebra.restrictScalars (g.comp f) B) where
  toChainHom := ChainDGAlgebra.RestrictScalars.compInv f g B.toChainDGAlgebra
  map_gamma := compInv_map_gamma f g B

/-- The chain-DGA map underlying the forward divided-power comparison is the canonical forward
chain comparison. -/
@[simp]
theorem compHom_toChainHom (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    (compHom f g B).toChainHom = (compChainIso f g B).hom := sorry

/-- The chain-DGA map underlying the inverse divided-power comparison is the canonical inverse
chain comparison. -/
@[simp]
theorem compInv_toChainHom (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    (compInv f g B).toChainHom = (compChainIso f g B).inv := sorry

/-- The forward divided-power composition comparison acts as the identity in every degree. -/
@[simp]
theorem compHom_apply (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) (n : ℤ)
    (x : (DividedPowerChainAlgebra.restrictScalars (g.comp f) B).toChainDGAlgebra.X n) :
    compHom f g B n x = x := sorry

/-- The inverse divided-power composition comparison acts as the identity in every degree. -/
@[simp]
theorem compInv_apply (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) (n : ℤ)
    (x : (DividedPowerChainAlgebra.restrictScalars f
      (DividedPowerChainAlgebra.restrictScalars g B)).toChainDGAlgebra.X n) :
    compInv f g B n x = x := sorry

/-- The forward divided-power comparison followed by its inverse is the identity. -/
@[simp]
theorem compHom_compInv (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    compHom f g B ≫ compInv f g B =
      𝟙 (DividedPowerChainAlgebra.restrictScalars (g.comp f) B) := sorry

/-- The inverse divided-power comparison followed by the forward comparison is the identity. -/
@[simp]
theorem compInv_compHom (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    compInv f g B ≫ compHom f g B =
      𝟙 (DividedPowerChainAlgebra.restrictScalars f
        (DividedPowerChainAlgebra.restrictScalars g B)) := sorry

/-- The canonical divided-power chain-DGA isomorphism from direct restriction along `g.comp f`
to successive restriction along `g` and then `f`. -/
@[stacks 09PQ "composition of restriction of scalars for divided-power chain DGAs"]
def compIso (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    DividedPowerChainAlgebra.restrictScalars (g.comp f) B ≅
      DividedPowerChainAlgebra.restrictScalars f
        (DividedPowerChainAlgebra.restrictScalars g B) where
  hom := compHom f g B
  inv := compInv f g B
  hom_inv_id := compHom_compInv f g B
  inv_hom_id := compInv_compHom f g B

/-- The forward morphism of the divided-power composition isomorphism is the explicit forward
comparison. -/
@[simp]
theorem compIso_hom (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    (compIso f g B).hom = compHom f g B := sorry

/-- The inverse morphism of the divided-power composition isomorphism is the explicit inverse
comparison. -/
@[simp]
theorem compIso_inv (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    (compIso f g B).inv = compInv f g B := sorry

/-- The chain-DGA morphism underlying the forward divided-power isomorphism is the generic
composition comparison. -/
@[simp]
theorem compIso_hom_toChainHom (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    (compIso f g B).hom.toChainHom = (compChainIso f g B).hom := sorry

/-- The chain-DGA morphism underlying the inverse divided-power isomorphism is the generic inverse
composition comparison. -/
@[simp]
theorem compIso_inv_toChainHom (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) :
    (compIso f g B).inv.toChainHom = (compChainIso f g B).inv := sorry

/-- The forward morphism of the divided-power composition isomorphism acts as the identity in
every degree. -/
@[simp]
theorem compIso_hom_apply (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) (n : ℤ)
    (x : (DividedPowerChainAlgebra.restrictScalars (g.comp f) B).toChainDGAlgebra.X n) :
    (compIso f g B).hom.toChainHom n x = x := sorry

/-- The inverse morphism of the divided-power composition isomorphism acts as the identity in
every degree. -/
@[simp]
theorem compIso_inv_apply (f : R →+* S) (g : S →+* T)
    (B : DividedPowerChainAlgebra.{uT, uB} T) (n : ℤ)
    (x : (DividedPowerChainAlgebra.restrictScalars f
      (DividedPowerChainAlgebra.restrictScalars g B)).toChainDGAlgebra.X n) :
    (compIso f g B).inv.toChainHom n x = x := sorry

/-- The forward divided-power composition comparison is natural in divided-power morphisms. -/
theorem compIso_hom_naturality (f : R →+* S) (g : S →+* T)
    {B C : DividedPowerChainAlgebra.{uT, uB} T} (phi : B ⟶ C) :
    DividedPowerChainAlgebra.Hom.restrictScalars (g.comp f) phi ≫ (compIso f g C).hom =
      (compIso f g B).hom ≫
        DividedPowerChainAlgebra.Hom.restrictScalars f
          (DividedPowerChainAlgebra.Hom.restrictScalars g phi) := sorry

/-- The inverse divided-power composition comparison is natural in divided-power morphisms. -/
theorem compIso_inv_naturality (f : R →+* S) (g : S →+* T)
    {B C : DividedPowerChainAlgebra.{uT, uB} T} (phi : B ⟶ C) :
    DividedPowerChainAlgebra.Hom.restrictScalars f
          (DividedPowerChainAlgebra.Hom.restrictScalars g phi) ≫ (compIso f g C).inv =
      (compIso f g B).inv ≫
        DividedPowerChainAlgebra.Hom.restrictScalars (g.comp f) phi := sorry

end Composition

section Coherence

variable {R : Type uR} {S : Type uS} {T : Type uT} {U : Type uU}
  [CommRing R] [CommRing S] [CommRing T] [CommRing U]

/-- The two forward divided-power composition comparisons for three successive restrictions
agree. -/
theorem compIso_hom_assoc (f : R →+* S) (g : S →+* T) (h : T →+* U)
    (B : DividedPowerChainAlgebra.{uU, uB} U) :
    (compIso f (h.comp g) B).hom ≫
        DividedPowerChainAlgebra.Hom.restrictScalars f (compIso g h B).hom =
      (compIso (g.comp f) h B).hom ≫
        (compIso f g (DividedPowerChainAlgebra.restrictScalars h B)).hom := sorry

/-- The two inverse divided-power composition comparisons for three successive restrictions
agree. -/
theorem compIso_inv_assoc (f : R →+* S) (g : S →+* T) (h : T →+* U)
    (B : DividedPowerChainAlgebra.{uU, uB} U) :
    DividedPowerChainAlgebra.Hom.restrictScalars f (compIso g h B).inv ≫
        (compIso f (h.comp g) B).inv =
      (compIso f g (DividedPowerChainAlgebra.restrictScalars h B)).inv ≫
        (compIso (g.comp f) h B).inv := sorry

end Coherence

end DividedPowerChainAlgebra.RestrictScalars
