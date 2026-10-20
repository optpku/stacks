module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.RestrictScalars.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Congruence for restriction of scalars on chain DGAs

Equal coefficient-ring homomorphisms induce canonically isomorphic restrictions of scalars.
The comparison is inherited degreewise from `ModuleCat.restrictScalarsCongr`, so both directions
act as the identity on every homogeneous element.  The objectwise comparisons assemble into a
natural isomorphism between the corresponding chain-DGA restriction functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uR uS uB

namespace ChainDGAlgebra.RestrictScalars

section Congruence

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
variable {f g k : R →+* S}

/-- The degreewise module isomorphism comparing restriction along equal coefficient-ring
homomorphisms. -/
@[stacks 09PQ "degreewise congruence for chain-DGA restriction of scalars"]
def congrComponentIso (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) (n : ℤ) :
    (B.restrictScalars f).X n ≅ (B.restrictScalars g).X n :=
  (ModuleCat.restrictScalarsCongr h).app (B.X n)

/-- The forward degreewise congruence comparison acts as the identity. -/
@[simp]
theorem congrComponentIso_hom_apply (h : f = g) (B : ChainDGAlgebra.{uS, uB} S)
    (n : ℤ) (x : (B.restrictScalars f).X n) :
    (congrComponentIso h B n).hom x = x := sorry

/-- The inverse degreewise congruence comparison acts as the identity. -/
@[simp]
theorem congrComponentIso_inv_apply (h : f = g) (B : ChainDGAlgebra.{uS, uB} S)
    (n : ℤ) (x : (B.restrictScalars g).X n) :
    (congrComponentIso h B n).inv x = x := sorry

/-- Reversing an equality reverses its degreewise restriction comparison. -/
@[simp]
theorem congrComponentIso_symm (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) (n : ℤ) :
    (congrComponentIso h B n).symm = congrComponentIso h.symm B n := sorry

/-- Degreewise restriction comparisons respect transitivity of equality. -/
theorem congrComponentIso_trans (h : f = g) (h' : g = k)
    (B : ChainDGAlgebra.{uS, uB} S) (n : ℤ) :
    congrComponentIso (h.trans h') B n =
      (congrComponentIso h B n).trans (congrComponentIso h' B n) := sorry

/-- The reflexive degreewise restriction comparison is the identity isomorphism. -/
@[simp]
theorem congrComponentIso_refl (B : ChainDGAlgebra.{uS, uB} S) (n : ℤ) :
    congrComponentIso (rfl : f = f) B n = Iso.refl _ := sorry

/-- The forward degreewise congruence comparisons commute with the differentials. -/
theorem congrComponentIso_hom_comm (h : f = g) (B : ChainDGAlgebra.{uS, uB} S)
    (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    (congrComponentIso h B i).hom ≫ (B.restrictScalars g).toChainComplex.d i j =
      (B.restrictScalars f).toChainComplex.d i j ≫
        (congrComponentIso h B j).hom := sorry

/-- The inverse degreewise congruence comparisons commute with the differentials. -/
theorem congrComponentIso_inv_comm (h : f = g) (B : ChainDGAlgebra.{uS, uB} S)
    (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    (congrComponentIso h B i).inv ≫ (B.restrictScalars f).toChainComplex.d i j =
      (B.restrictScalars g).toChainComplex.d i j ≫
        (congrComponentIso h B j).inv := sorry

/-- The chain map comparing restriction along equal coefficient-ring homomorphisms. -/
@[stacks 09PQ "chain-map congruence for chain-DGA restriction of scalars"]
def congrHomChainMap (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (B.restrictScalars f).toChainComplex ⟶
      (B.restrictScalars g).toChainComplex where
  f n := (congrComponentIso h B n).hom
  comm' := congrComponentIso_hom_comm h B

/-- The inverse chain map comparing restriction along equal coefficient-ring homomorphisms. -/
@[stacks 09PQ "inverse chain-map congruence for chain-DGA restriction of scalars"]
def congrInvChainMap (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (B.restrictScalars g).toChainComplex ⟶
      (B.restrictScalars f).toChainComplex where
  f n := (congrComponentIso h B n).inv
  comm' := congrComponentIso_inv_comm h B

/-- The forward congruence chain map has the Mathlib comparison in every degree. -/
@[simp]
theorem congrHomChainMap_f (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) (n : ℤ) :
    (congrHomChainMap h B).f n = (congrComponentIso h B n).hom := sorry

/-- The inverse congruence chain map has the inverse Mathlib comparison in every degree. -/
@[simp]
theorem congrInvChainMap_f (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) (n : ℤ) :
    (congrInvChainMap h B).f n = (congrComponentIso h B n).inv := sorry

/-- The forward congruence chain map acts as the identity in every degree. -/
@[simp]
theorem congrHomChainMap_apply (h : f = g) (B : ChainDGAlgebra.{uS, uB} S)
    (n : ℤ) (x : (B.restrictScalars f).X n) :
    (congrHomChainMap h B).f n x = x := sorry

/-- The inverse congruence chain map acts as the identity in every degree. -/
@[simp]
theorem congrInvChainMap_apply (h : f = g) (B : ChainDGAlgebra.{uS, uB} S)
    (n : ℤ) (x : (B.restrictScalars g).X n) :
    (congrInvChainMap h B).f n x = x := sorry

/-- The forward and inverse congruence chain maps compose to the source identity. -/
@[simp]
theorem congrHomChainMap_compInv (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    congrHomChainMap h B ≫ congrInvChainMap h B =
      𝟙 (B.restrictScalars f).toChainComplex := sorry

/-- The inverse and forward congruence chain maps compose to the target identity. -/
@[simp]
theorem congrInvChainMap_compHom (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    congrInvChainMap h B ≫ congrHomChainMap h B =
      𝟙 (B.restrictScalars g).toChainComplex := sorry

/-- The canonical complex isomorphism comparing restriction along equal coefficient-ring
homomorphisms. -/
@[stacks 09PQ "complex congruence for chain-DGA restriction of scalars"]
def congrComplexIso (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (B.restrictScalars f).toChainComplex ≅
      (B.restrictScalars g).toChainComplex where
  hom := congrHomChainMap h B
  inv := congrInvChainMap h B
  hom_inv_id := congrHomChainMap_compInv h B
  inv_hom_id := congrInvChainMap_compHom h B

/-- The forward map of the complex congruence is the explicit forward chain map. -/
@[simp]
theorem congrComplexIso_hom (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (congrComplexIso h B).hom = congrHomChainMap h B := sorry

/-- The inverse map of the complex congruence is the explicit inverse chain map. -/
@[simp]
theorem congrComplexIso_inv (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (congrComplexIso h B).inv = congrInvChainMap h B := sorry

/-- Reversing an equality reverses the underlying-complex restriction comparison. -/
@[simp]
theorem congrComplexIso_symm (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (congrComplexIso h B).symm = congrComplexIso h.symm B := sorry

/-- Underlying-complex restriction comparisons respect transitivity of equality. -/
theorem congrComplexIso_trans (h : f = g) (h' : g = k)
    (B : ChainDGAlgebra.{uS, uB} S) :
    congrComplexIso (h.trans h') B =
      (congrComplexIso h B).trans (congrComplexIso h' B) := sorry

/-- The forward congruence chain map preserves the homogeneous unit. -/
theorem congrHomChainMap_one (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (congrHomChainMap h B).f 0 (B.restrictScalars f).one =
      (B.restrictScalars g).one := sorry

/-- The forward congruence chain map preserves homogeneous multiplication. -/
theorem congrHomChainMap_mul (h : f = g) (B : ChainDGAlgebra.{uS, uB} S)
    (n m : ℤ) (x : (B.restrictScalars f).X n)
    (y : (B.restrictScalars f).X m) :
    (congrHomChainMap h B).f (n + m) ((B.restrictScalars f).mul n m x y) =
      (B.restrictScalars g).mul n m
        ((congrHomChainMap h B).f n x) ((congrHomChainMap h B).f m y) := sorry

/-- The inverse congruence chain map preserves the homogeneous unit. -/
theorem congrInvChainMap_one (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (congrInvChainMap h B).f 0 (B.restrictScalars g).one =
      (B.restrictScalars f).one := sorry

/-- The inverse congruence chain map preserves homogeneous multiplication. -/
theorem congrInvChainMap_mul (h : f = g) (B : ChainDGAlgebra.{uS, uB} S)
    (n m : ℤ) (x : (B.restrictScalars g).X n)
    (y : (B.restrictScalars g).X m) :
    (congrInvChainMap h B).f (n + m) ((B.restrictScalars g).mul n m x y) =
      (B.restrictScalars f).mul n m
        ((congrInvChainMap h B).f n x) ((congrInvChainMap h B).f m y) := sorry

/-- The chain-DGA homomorphism comparing restriction along equal coefficient-ring
homomorphisms. -/
@[stacks 09PQ "chain-DGA congruence for restriction of scalars"]
def congrHom (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    ChainDGAlgebra.Hom (B.restrictScalars f) (B.restrictScalars g) where
  toChainMap := congrHomChainMap h B
  map_one := congrHomChainMap_one h B
  map_mul := congrHomChainMap_mul h B

/-- The inverse chain-DGA homomorphism comparing restriction along equal coefficient-ring
homomorphisms. -/
@[stacks 09PQ "inverse chain-DGA congruence for restriction of scalars"]
def congrInv (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    ChainDGAlgebra.Hom (B.restrictScalars g) (B.restrictScalars f) where
  toChainMap := congrInvChainMap h B
  map_one := congrInvChainMap_one h B
  map_mul := congrInvChainMap_mul h B

/-- The underlying chain map of the forward chain-DGA congruence is the complex comparison. -/
@[simp]
theorem congrHom_toChainMap (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (congrHom h B).toChainMap = (congrComplexIso h B).hom := sorry

/-- The underlying chain map of the inverse chain-DGA congruence is the inverse complex
comparison. -/
@[simp]
theorem congrInv_toChainMap (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (congrInv h B).toChainMap = (congrComplexIso h B).inv := sorry

/-- The forward chain-DGA congruence acts as the identity in every degree. -/
@[simp]
theorem congrHom_apply (h : f = g) (B : ChainDGAlgebra.{uS, uB} S)
    (n : ℤ) (x : (B.restrictScalars f).X n) :
    congrHom h B n x = x := sorry

/-- The inverse chain-DGA congruence acts as the identity in every degree. -/
@[simp]
theorem congrInv_apply (h : f = g) (B : ChainDGAlgebra.{uS, uB} S)
    (n : ℤ) (x : (B.restrictScalars g).X n) :
    congrInv h B n x = x := sorry

/-- The forward chain-DGA congruence followed by its inverse is the identity. -/
@[simp]
theorem congrHom_compInv (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    congrHom h B ≫ congrInv h B = 𝟙 (B.restrictScalars f) := sorry

/-- The inverse chain-DGA congruence followed by the forward comparison is the identity. -/
@[simp]
theorem congrInv_compHom (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    congrInv h B ≫ congrHom h B = 𝟙 (B.restrictScalars g) := sorry

/-- The canonical chain-DGA isomorphism comparing restriction along equal coefficient-ring
homomorphisms. -/
@[stacks 09PQ "congruence for chain-DGA restriction of scalars"]
def congrIso (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    B.restrictScalars f ≅ B.restrictScalars g where
  hom := congrHom h B
  inv := congrInv h B
  hom_inv_id := congrHom_compInv h B
  inv_hom_id := congrInv_compHom h B

/-- The forward morphism of the chain-DGA congruence isomorphism is the explicit comparison. -/
@[simp]
theorem congrIso_hom (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (congrIso h B).hom = congrHom h B := sorry

/-- The inverse morphism of the chain-DGA congruence isomorphism is the explicit inverse. -/
@[simp]
theorem congrIso_inv (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (congrIso h B).inv = congrInv h B := sorry

/-- The forward morphism of the chain-DGA congruence isomorphism acts as the identity in every
degree. -/
@[simp]
theorem congrIso_hom_apply (h : f = g) (B : ChainDGAlgebra.{uS, uB} S)
    (n : ℤ) (x : (B.restrictScalars f).X n) :
    (congrIso h B).hom n x = x := sorry

/-- The inverse morphism of the chain-DGA congruence isomorphism acts as the identity in every
degree. -/
@[simp]
theorem congrIso_inv_apply (h : f = g) (B : ChainDGAlgebra.{uS, uB} S)
    (n : ℤ) (x : (B.restrictScalars g).X n) :
    (congrIso h B).inv n x = x := sorry

/-- The forward restriction congruence is natural in chain-DGA morphisms. -/
theorem congrIso_hom_naturality (h : f = g)
    {B C : ChainDGAlgebra.{uS, uB} S} (phi : B ⟶ C) :
    map f phi ≫ (congrIso h C).hom =
      (congrIso h B).hom ≫ map g phi := sorry

/-- The inverse restriction congruence is natural in chain-DGA morphisms. -/
theorem congrIso_inv_naturality (h : f = g)
    {B C : ChainDGAlgebra.{uS, uB} S} (phi : B ⟶ C) :
    map g phi ≫ (congrIso h C).inv =
      (congrIso h B).inv ≫ map f phi := sorry

/-- Restricting a chain-DGA morphism along equal ring homomorphisms differs only by the canonical
source and target comparisons. -/
theorem map_congr (h : f = g) {B C : ChainDGAlgebra.{uS, uB} S} (phi : B ⟶ C) :
    map f phi =
      (congrIso h B).hom ≫ map g phi ≫ (congrIso h C).inv := sorry

/-- Reversing an equality reverses the chain-DGA restriction comparison. -/
@[simp]
theorem congrIso_symm (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (congrIso h B).symm = congrIso h.symm B := sorry

/-- Chain-DGA restriction comparisons respect transitivity of equality. -/
theorem congrIso_trans (h : f = g) (h' : g = k)
    (B : ChainDGAlgebra.{uS, uB} S) :
    congrIso (h.trans h') B = (congrIso h B).trans (congrIso h' B) := sorry

/-- The reflexive chain-DGA restriction comparison is the identity isomorphism. -/
@[simp]
theorem congrIso_refl (B : ChainDGAlgebra.{uS, uB} S) :
    congrIso (rfl : f = f) B = Iso.refl _ := sorry

/-- Equal coefficient-ring homomorphisms induce naturally isomorphic chain-DGA restriction
functors. -/
@[stacks 09PQ "natural congruence for chain-DGA restriction-of-scalars functors"]
def functorIso (h : f = g) :
    functor.{uR, uS, uB} f ≅ functor.{uR, uS, uB} g :=
  NatIso.ofComponents (fun B ↦ congrIso h B) (congrIso_hom_naturality h)

/-- A component of the restriction-functor congruence is the objectwise chain-DGA
comparison. -/
@[simp]
theorem functorIso_app (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (functorIso.{uR, uS, uB} h).app B = congrIso h B := sorry

/-- The forward natural-transformation component is the explicit chain-DGA congruence. -/
@[simp]
theorem functorIso_hom_app (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (functorIso.{uR, uS, uB} h).hom.app B = congrHom h B := sorry

/-- The inverse natural-transformation component is the explicit inverse chain-DGA
congruence. -/
@[simp]
theorem functorIso_inv_app (h : f = g) (B : ChainDGAlgebra.{uS, uB} S) :
    (functorIso.{uR, uS, uB} h).inv.app B = congrInv h B := sorry

/-- Reversing an equality reverses the restriction-functor congruence. -/
@[simp]
theorem functorIso_symm (h : f = g) :
    (functorIso.{uR, uS, uB} h).symm = functorIso.{uR, uS, uB} h.symm := sorry

/-- Restriction-functor congruences respect transitivity of equality. -/
theorem functorIso_trans (h : f = g) (h' : g = k) :
    functorIso.{uR, uS, uB} (h.trans h') =
      (functorIso.{uR, uS, uB} h).trans (functorIso.{uR, uS, uB} h') := sorry

/-- The reflexive restriction-functor congruence is the identity natural isomorphism. -/
@[simp]
theorem functorIso_refl :
    functorIso.{uR, uS, uB} (rfl : f = f) = Iso.refl _ := sorry

end Congruence

end ChainDGAlgebra.RestrictScalars
