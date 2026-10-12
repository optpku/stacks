/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.RestrictScalars.Congr
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.RestrictScalars.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Congruence for restriction of scalars on divided-power chain DGAs

The canonical congruence comparison for chain DGAs preserves the unchanged divided-power
operations.  It therefore lifts to divided-power chain DGAs without changing its action on any
homogeneous element.  The objectwise lifts assemble into a natural isomorphism between the
corresponding divided-power restriction functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uR uS uB

namespace DividedPowerChainAlgebra.RestrictScalars

section Congruence

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
variable {f g k : R →+* S}

/-- The chain-DGA congruence isomorphism underlying restriction of a divided-power chain DGA
along equal coefficient-ring homomorphisms. -/
@[stacks 09PQ "underlying chain-DGA congruence for divided-power restriction of scalars"]
def congrChainIso (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (DividedPowerChainAlgebra.restrictScalars f B).toChainDGAlgebra ≅
      (DividedPowerChainAlgebra.restrictScalars g B).toChainDGAlgebra :=
  ChainDGAlgebra.RestrictScalars.congrIso h B.toChainDGAlgebra

/-- The chain-complex congruence isomorphism underlying restriction of a divided-power chain DGA
along equal coefficient-ring homomorphisms. -/
@[stacks 09PQ "underlying complex congruence for divided-power restriction of scalars"]
def congrComplexIso (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (DividedPowerChainAlgebra.restrictScalars f B).toChainDGAlgebra.toChainComplex ≅
      (DividedPowerChainAlgebra.restrictScalars g B).toChainDGAlgebra.toChainComplex :=
  ChainDGAlgebra.RestrictScalars.congrComplexIso h B.toChainDGAlgebra

/-- The forward underlying chain-DGA comparison is the generic congruence comparison. -/
@[simp]
theorem congrChainIso_hom (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (congrChainIso h B).hom =
      ChainDGAlgebra.RestrictScalars.congrHom h B.toChainDGAlgebra := sorry

/-- The inverse underlying chain-DGA comparison is the generic inverse congruence comparison. -/
@[simp]
theorem congrChainIso_inv (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (congrChainIso h B).inv =
      ChainDGAlgebra.RestrictScalars.congrInv h B.toChainDGAlgebra := sorry

/-- The forward underlying complex comparison is the generic congruence chain map. -/
@[simp]
theorem congrComplexIso_hom (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (congrComplexIso h B).hom =
      ChainDGAlgebra.RestrictScalars.congrHomChainMap h B.toChainDGAlgebra := sorry

/-- The inverse underlying complex comparison is the generic inverse congruence chain map. -/
@[simp]
theorem congrComplexIso_inv (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (congrComplexIso h B).inv =
      ChainDGAlgebra.RestrictScalars.congrInvChainMap h B.toChainDGAlgebra := sorry

/-- The generic forward congruence comparison preserves the divided powers of the restricted
objects. -/
theorem congrHom_map_gamma (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S)
    (n : ℕ)
    (x : (DividedPowerChainAlgebra.restrictScalars f B).toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (ChainDGAlgebra.RestrictScalars.congrHom h B.toChainDGAlgebra).nonnegativePart.evenMap
        ((DividedPowerChainAlgebra.restrictScalars f B).gamma n x) =
      (DividedPowerChainAlgebra.restrictScalars g B).gamma n
        ((ChainDGAlgebra.RestrictScalars.congrHom h
          B.toChainDGAlgebra).nonnegativePart.evenPositiveMap x) := sorry

/-- The generic inverse congruence comparison preserves the divided powers of the restricted
objects. -/
theorem congrInv_map_gamma (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S)
    (n : ℕ)
    (x : (DividedPowerChainAlgebra.restrictScalars g B).toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (ChainDGAlgebra.RestrictScalars.congrInv h B.toChainDGAlgebra).nonnegativePart.evenMap
        ((DividedPowerChainAlgebra.restrictScalars g B).gamma n x) =
      (DividedPowerChainAlgebra.restrictScalars f B).gamma n
        ((ChainDGAlgebra.RestrictScalars.congrInv h
          B.toChainDGAlgebra).nonnegativePart.evenPositiveMap x) := sorry

/-- The forward divided-power morphism comparing restriction along equal coefficient-ring
homomorphisms. -/
@[stacks 09PQ "forward congruence for divided-power chain-DGA restriction"]
def congrHom (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    DividedPowerChainAlgebra.Hom
      (DividedPowerChainAlgebra.restrictScalars f B)
      (DividedPowerChainAlgebra.restrictScalars g B) where
  toChainHom := ChainDGAlgebra.RestrictScalars.congrHom h B.toChainDGAlgebra
  map_gamma := congrHom_map_gamma h B

/-- The inverse divided-power morphism comparing restriction along equal coefficient-ring
homomorphisms. -/
@[stacks 09PQ "inverse congruence for divided-power chain-DGA restriction"]
def congrInv (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    DividedPowerChainAlgebra.Hom
      (DividedPowerChainAlgebra.restrictScalars g B)
      (DividedPowerChainAlgebra.restrictScalars f B) where
  toChainHom := ChainDGAlgebra.RestrictScalars.congrInv h B.toChainDGAlgebra
  map_gamma := congrInv_map_gamma h B

/-- The chain-DGA map underlying the forward divided-power congruence is the canonical generic
comparison. -/
@[simp]
theorem congrHom_toChainHom (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (congrHom h B).toChainHom = (congrChainIso h B).hom := sorry

/-- The chain-DGA map underlying the inverse divided-power congruence is the canonical generic
inverse. -/
@[simp]
theorem congrInv_toChainHom (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (congrInv h B).toChainHom = (congrChainIso h B).inv := sorry

/-- The forward divided-power congruence acts as the identity in every degree. -/
@[simp]
theorem congrHom_apply (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S)
    (n : ℤ)
    (x : (DividedPowerChainAlgebra.restrictScalars f B).toChainDGAlgebra.X n) :
    congrHom h B n x = x := sorry

/-- The inverse divided-power congruence acts as the identity in every degree. -/
@[simp]
theorem congrInv_apply (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S)
    (n : ℤ)
    (x : (DividedPowerChainAlgebra.restrictScalars g B).toChainDGAlgebra.X n) :
    congrInv h B n x = x := sorry

/-- The forward divided-power congruence followed by its inverse is the identity. -/
@[simp]
theorem congrHom_compInv (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    congrHom h B ≫ congrInv h B =
      𝟙 (DividedPowerChainAlgebra.restrictScalars f B) := sorry

/-- The inverse divided-power congruence followed by the forward comparison is the identity. -/
@[simp]
theorem congrInv_compHom (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    congrInv h B ≫ congrHom h B =
      𝟙 (DividedPowerChainAlgebra.restrictScalars g B) := sorry

/-- The canonical divided-power chain-DGA isomorphism comparing restriction along equal
coefficient-ring homomorphisms. -/
@[stacks 09PQ "congruence for divided-power chain-DGA restriction of scalars"]
def congrIso (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    DividedPowerChainAlgebra.restrictScalars f B ≅
      DividedPowerChainAlgebra.restrictScalars g B where
  hom := congrHom h B
  inv := congrInv h B
  hom_inv_id := congrHom_compInv h B
  inv_hom_id := congrInv_compHom h B

/-- The forward morphism of the divided-power congruence isomorphism is the explicit forward
comparison. -/
@[simp]
theorem congrIso_hom (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (congrIso h B).hom = congrHom h B := sorry

/-- The inverse morphism of the divided-power congruence isomorphism is the explicit inverse
comparison. -/
@[simp]
theorem congrIso_inv (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (congrIso h B).inv = congrInv h B := sorry

/-- The chain-DGA morphism underlying the forward divided-power congruence is the generic
comparison. -/
@[simp]
theorem congrIso_hom_toChainHom (h : f = g)
    (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (congrIso h B).hom.toChainHom = (congrChainIso h B).hom := sorry

/-- The chain-DGA morphism underlying the inverse divided-power congruence is the generic inverse
comparison. -/
@[simp]
theorem congrIso_inv_toChainHom (h : f = g)
    (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (congrIso h B).inv.toChainHom = (congrChainIso h B).inv := sorry

/-- The forward morphism of the divided-power congruence isomorphism acts as the identity in
every degree. -/
@[simp]
theorem congrIso_hom_apply (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S)
    (n : ℤ)
    (x : (DividedPowerChainAlgebra.restrictScalars f B).toChainDGAlgebra.X n) :
    (congrIso h B).hom.toChainHom n x = x := sorry

/-- The inverse morphism of the divided-power congruence isomorphism acts as the identity in
every degree. -/
@[simp]
theorem congrIso_inv_apply (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S)
    (n : ℤ)
    (x : (DividedPowerChainAlgebra.restrictScalars g B).toChainDGAlgebra.X n) :
    (congrIso h B).inv.toChainHom n x = x := sorry

/-- The forward divided-power restriction congruence is natural in divided-power morphisms. -/
theorem congrIso_hom_naturality (h : f = g)
    {B C : DividedPowerChainAlgebra.{uS, uB} S} (phi : B ⟶ C) :
    DividedPowerChainAlgebra.Hom.restrictScalars f phi ≫ (congrIso h C).hom =
      (congrIso h B).hom ≫
        DividedPowerChainAlgebra.Hom.restrictScalars g phi := sorry

/-- The inverse divided-power restriction congruence is natural in divided-power morphisms. -/
theorem congrIso_inv_naturality (h : f = g)
    {B C : DividedPowerChainAlgebra.{uS, uB} S} (phi : B ⟶ C) :
    DividedPowerChainAlgebra.Hom.restrictScalars g phi ≫ (congrIso h C).inv =
      (congrIso h B).inv ≫
        DividedPowerChainAlgebra.Hom.restrictScalars f phi := sorry

/-- Restricting a divided-power morphism along equal ring homomorphisms differs only by the
canonical source and target comparisons. -/
theorem map_congr (h : f = g)
    {B C : DividedPowerChainAlgebra.{uS, uB} S} (phi : B ⟶ C) :
    DividedPowerChainAlgebra.Hom.restrictScalars f phi =
      (congrIso h B).hom ≫
        DividedPowerChainAlgebra.Hom.restrictScalars g phi ≫
          (congrIso h C).inv := sorry

/-- Reversing an equality reverses the divided-power chain-DGA restriction comparison. -/
@[simp]
theorem congrIso_symm (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (congrIso h B).symm = congrIso h.symm B := sorry

/-- Divided-power chain-DGA restriction comparisons respect transitivity of equality. -/
theorem congrIso_trans (h : f = g) (h' : g = k)
    (B : DividedPowerChainAlgebra.{uS, uB} S) :
    congrIso (h.trans h') B = (congrIso h B).trans (congrIso h' B) := sorry

/-- The reflexive divided-power chain-DGA restriction comparison is the identity isomorphism. -/
@[simp]
theorem congrIso_refl (B : DividedPowerChainAlgebra.{uS, uB} S) :
    congrIso (rfl : f = f) B = Iso.refl _ := sorry

/-- Equal coefficient-ring homomorphisms induce naturally isomorphic divided-power chain-DGA
restriction functors. -/
@[stacks 09PQ "natural congruence for divided-power restriction-of-scalars functors"]
def functorIso (h : f = g) :
    DividedPowerChainAlgebra.restrictScalarsFunctor.{uR, uS, uB} f ≅
      DividedPowerChainAlgebra.restrictScalarsFunctor.{uR, uS, uB} g :=
  NatIso.ofComponents (fun B ↦ congrIso h B) (congrIso_hom_naturality h)

/-- A component of the divided-power restriction-functor congruence is the objectwise
comparison. -/
@[simp]
theorem functorIso_app (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (functorIso.{uR, uS, uB} h).app B = congrIso h B := sorry

/-- The forward natural-transformation component is the explicit divided-power congruence. -/
@[simp]
theorem functorIso_hom_app (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (functorIso.{uR, uS, uB} h).hom.app B = congrHom h B := sorry

/-- The inverse natural-transformation component is the explicit inverse divided-power
congruence. -/
@[simp]
theorem functorIso_inv_app (h : f = g) (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (functorIso.{uR, uS, uB} h).inv.app B = congrInv h B := sorry

/-- Reversing an equality reverses the divided-power restriction-functor congruence. -/
@[simp]
theorem functorIso_symm (h : f = g) :
    (functorIso.{uR, uS, uB} h).symm = functorIso.{uR, uS, uB} h.symm := sorry

/-- Divided-power restriction-functor congruences respect transitivity of equality. -/
theorem functorIso_trans (h : f = g) (h' : g = k) :
    functorIso.{uR, uS, uB} (h.trans h') =
      (functorIso.{uR, uS, uB} h).trans (functorIso.{uR, uS, uB} h') := sorry

/-- The reflexive divided-power restriction-functor congruence is the identity natural
isomorphism. -/
@[simp]
theorem functorIso_refl :
    functorIso.{uR, uS, uB} (rfl : f = f) = Iso.refl _ := sorry

end Congruence

end DividedPowerChainAlgebra.RestrictScalars
