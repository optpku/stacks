module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Category
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.RestrictScalars
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of restriction of scalars for chain DGAs

Restriction of scalars acts on chain-DGA morphisms and is canonically compatible with composition
of coefficient-ring homomorphisms.  The comparison is inherited degreewise from
`ModuleCat.restrictScalarsComp'App`; both directions therefore act as the identity on homogeneous
elements.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uR uS uT uU uB

namespace ChainDGAlgebra.RestrictScalars

section Map

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
variable {B C D : ChainDGAlgebra.{uS, uB} S}

/-- Apply module restriction degreewise to the chain map underlying a chain-DGA morphism. -/
def mapChainMap (sigma : R →+* S) (phi : ChainDGAlgebra.Hom B C) :
    (B.restrictScalars sigma).toChainComplex ⟶
      (C.restrictScalars sigma).toChainComplex :=
  ((ModuleCat.restrictScalars sigma).mapHomologicalComplex (ComplexShape.down ℤ)).map
    phi.toChainMap

/-- Restricting scalars does not change the degreewise action of a chain map. -/
@[simp]
theorem mapChainMap_apply (sigma : R →+* S) (phi : ChainDGAlgebra.Hom B C)
    (n : ℤ) (x : (B.restrictScalars sigma).X n) :
    (mapChainMap sigma phi).f n x = phi n x := sorry

/-- The restricted chain map preserves the homogeneous unit. -/
theorem mapChainMap_one (sigma : R →+* S) (phi : ChainDGAlgebra.Hom B C) :
    (mapChainMap sigma phi).f 0 (B.restrictScalars sigma).one =
      (C.restrictScalars sigma).one := sorry

/-- The restricted chain map preserves homogeneous multiplication. -/
theorem mapChainMap_mul (sigma : R →+* S) (phi : ChainDGAlgebra.Hom B C)
    (n m : ℤ) (x : (B.restrictScalars sigma).X n)
    (y : (B.restrictScalars sigma).X m) :
    (mapChainMap sigma phi).f (n + m) ((B.restrictScalars sigma).mul n m x y) =
      (C.restrictScalars sigma).mul n m
        ((mapChainMap sigma phi).f n x) ((mapChainMap sigma phi).f m y) := sorry

/-- Restrict both the source and target scalars of a chain-DGA morphism. -/
@[stacks 09PQ "restriction of scalars on chain-DGA morphisms"]
def map (sigma : R →+* S) (phi : ChainDGAlgebra.Hom B C) :
    ChainDGAlgebra.Hom (B.restrictScalars sigma) (C.restrictScalars sigma) where
  toChainMap := mapChainMap sigma phi
  map_one := mapChainMap_one sigma phi
  map_mul := mapChainMap_mul sigma phi

/-- Restriction of scalars leaves the pointwise action of a chain-DGA morphism unchanged. -/
@[simp]
theorem map_apply (sigma : R →+* S) (phi : ChainDGAlgebra.Hom B C)
    (n : ℤ) (x : (B.restrictScalars sigma).X n) :
    map sigma phi n x = phi n x := sorry

/-- Restriction of scalars preserves identity chain-DGA morphisms. -/
@[simp]
theorem map_id (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S) :
    map sigma (𝟙 B) = 𝟙 (B.restrictScalars sigma) := sorry

/-- Restriction of scalars preserves composition of chain-DGA morphisms. -/
@[simp]
theorem map_comp (sigma : R →+* S) (phi : B ⟶ C) (psi : C ⟶ D) :
    map sigma (ChainDGAlgebra.Hom.comp psi phi) =
      ChainDGAlgebra.Hom.comp (map sigma psi) (map sigma phi) := sorry

/-- Restriction of scalars is functorial on chain DGAs with a fixed carrier universe. -/
@[stacks 09PQ "restriction-of-scalars functor for chain DGAs"]
def functor (sigma : R →+* S) :
    ChainDGAlgebra.{uS, uB} S ⥤ ChainDGAlgebra.{uR, uB} R where
  obj B := B.restrictScalars sigma
  map phi := map sigma phi
  map_id B := map_id sigma B
  map_comp phi psi := map_comp sigma phi psi

end Map

section Composition

variable {R : Type uR} {S : Type uS} {T : Type uT}
  [CommRing R] [CommRing S] [CommRing T]

/-- The degreewise module isomorphism from direct restriction along `g.comp f` to successive
restriction along `g` and then `f`. -/
def compComponentIso (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (n : ℤ) :
    (B.restrictScalars (g.comp f)).X n ≅
      ((B.restrictScalars g).restrictScalars f).X n :=
  ModuleCat.restrictScalarsComp'App f g (g.comp f) rfl (B.X n)

/-- The forward composition comparison acts as the identity in each degree. -/
@[simp]
theorem compComponentIso_hom_apply (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (n : ℤ)
    (x : (B.restrictScalars (g.comp f)).X n) :
    (compComponentIso f g B n).hom x = x := sorry

/-- The inverse composition comparison acts as the identity in each degree. -/
@[simp]
theorem compComponentIso_inv_apply (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (n : ℤ)
    (x : ((B.restrictScalars g).restrictScalars f).X n) :
    (compComponentIso f g B n).inv x = x := sorry

/-- The forward degreewise composition comparisons commute with the differentials. -/
theorem compComponentIso_hom_comm (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) :
    (compComponentIso f g B i).hom ≫
        ((B.restrictScalars g).restrictScalars f).toChainComplex.d i j =
      (B.restrictScalars (g.comp f)).toChainComplex.d i j ≫
        (compComponentIso f g B j).hom := sorry

/-- The inverse degreewise composition comparisons commute with the differentials. -/
theorem compComponentIso_inv_comm (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) :
    (compComponentIso f g B i).inv ≫
        (B.restrictScalars (g.comp f)).toChainComplex.d i j =
      ((B.restrictScalars g).restrictScalars f).toChainComplex.d i j ≫
        (compComponentIso f g B j).inv := sorry

/-- The chain map from direct restriction along a composite to successive restriction. -/
def compHomChainMap (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    (B.restrictScalars (g.comp f)).toChainComplex ⟶
      ((B.restrictScalars g).restrictScalars f).toChainComplex where
  f n := (compComponentIso f g B n).hom
  comm' := compComponentIso_hom_comm f g B

/-- The chain map from successive restriction back to direct restriction along the composite. -/
def compInvChainMap (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    ((B.restrictScalars g).restrictScalars f).toChainComplex ⟶
      (B.restrictScalars (g.comp f)).toChainComplex where
  f n := (compComponentIso f g B n).inv
  comm' := compComponentIso_inv_comm f g B

/-- The forward comparison chain map has the Mathlib composition comparison in every degree. -/
@[simp]
theorem compHomChainMap_f (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (n : ℤ) :
    (compHomChainMap f g B).f n = (compComponentIso f g B n).hom := sorry

/-- The inverse comparison chain map has the inverse Mathlib comparison in every degree. -/
@[simp]
theorem compInvChainMap_f (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (n : ℤ) :
    (compInvChainMap f g B).f n = (compComponentIso f g B n).inv := sorry

/-- The forward and inverse comparison chain maps compose to the direct-restriction identity. -/
@[simp]
theorem compHomChainMap_compInv (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    compHomChainMap f g B ≫ compInvChainMap f g B =
      𝟙 (B.restrictScalars (g.comp f)).toChainComplex := sorry

/-- The inverse and forward comparison chain maps compose to the iterated-restriction identity. -/
@[simp]
theorem compInvChainMap_compHom (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    compInvChainMap f g B ≫ compHomChainMap f g B =
      𝟙 ((B.restrictScalars g).restrictScalars f).toChainComplex := sorry

/-- The canonical underlying-complex comparison between direct and successive restriction. -/
@[stacks 09PQ "composition of restriction of scalars on chain complexes"]
def compComplexIso (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    (B.restrictScalars (g.comp f)).toChainComplex ≅
      ((B.restrictScalars g).restrictScalars f).toChainComplex where
  hom := compHomChainMap f g B
  inv := compInvChainMap f g B
  hom_inv_id := compHomChainMap_compInv f g B
  inv_hom_id := compInvChainMap_compHom f g B

/-- The forward comparison chain map preserves the homogeneous unit. -/
theorem compHomChainMap_one (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    (compHomChainMap f g B).f 0 (B.restrictScalars (g.comp f)).one =
      ((B.restrictScalars g).restrictScalars f).one := sorry

/-- The forward comparison chain map preserves homogeneous multiplication. -/
theorem compHomChainMap_mul (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (n m : ℤ)
    (x : (B.restrictScalars (g.comp f)).X n)
    (y : (B.restrictScalars (g.comp f)).X m) :
    (compHomChainMap f g B).f (n + m)
        ((B.restrictScalars (g.comp f)).mul n m x y) =
      ((B.restrictScalars g).restrictScalars f).mul n m
        ((compHomChainMap f g B).f n x) ((compHomChainMap f g B).f m y) := sorry

/-- The inverse comparison chain map preserves the homogeneous unit. -/
theorem compInvChainMap_one (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    (compInvChainMap f g B).f 0 ((B.restrictScalars g).restrictScalars f).one =
      (B.restrictScalars (g.comp f)).one := sorry

/-- The inverse comparison chain map preserves homogeneous multiplication. -/
theorem compInvChainMap_mul (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (n m : ℤ)
    (x : ((B.restrictScalars g).restrictScalars f).X n)
    (y : ((B.restrictScalars g).restrictScalars f).X m) :
    (compInvChainMap f g B).f (n + m)
        (((B.restrictScalars g).restrictScalars f).mul n m x y) =
      (B.restrictScalars (g.comp f)).mul n m
        ((compInvChainMap f g B).f n x) ((compInvChainMap f g B).f m y) := sorry

/-- The chain-DGA homomorphism from direct restriction along a composite to successive
restriction. -/
@[stacks 09PQ "forward composition comparison for chain-DGA restriction"]
def compHom (f : R →+* S) (g : S →+* T) (B : ChainDGAlgebra.{uT, uB} T) :
    ChainDGAlgebra.Hom (B.restrictScalars (g.comp f))
      ((B.restrictScalars g).restrictScalars f) where
  toChainMap := compHomChainMap f g B
  map_one := compHomChainMap_one f g B
  map_mul := compHomChainMap_mul f g B

/-- The chain-DGA homomorphism from successive restriction back to direct restriction along the
composite. -/
@[stacks 09PQ "inverse composition comparison for chain-DGA restriction"]
def compInv (f : R →+* S) (g : S →+* T) (B : ChainDGAlgebra.{uT, uB} T) :
    ChainDGAlgebra.Hom ((B.restrictScalars g).restrictScalars f)
      (B.restrictScalars (g.comp f)) where
  toChainMap := compInvChainMap f g B
  map_one := compInvChainMap_one f g B
  map_mul := compInvChainMap_mul f g B

/-- The underlying chain map of the forward chain-DGA comparison is the canonical complex
comparison. -/
@[simp]
theorem compHom_toChainMap (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    (compHom f g B).toChainMap = (compComplexIso f g B).hom := sorry

/-- The underlying chain map of the inverse chain-DGA comparison is the inverse complex
comparison. -/
@[simp]
theorem compInv_toChainMap (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    (compInv f g B).toChainMap = (compComplexIso f g B).inv := sorry

/-- The forward chain-DGA composition comparison acts as the identity in every degree. -/
@[simp]
theorem compHom_apply (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (n : ℤ)
    (x : (B.restrictScalars (g.comp f)).X n) :
    compHom f g B n x = x := sorry

/-- The inverse chain-DGA composition comparison acts as the identity in every degree. -/
@[simp]
theorem compInv_apply (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (n : ℤ)
    (x : ((B.restrictScalars g).restrictScalars f).X n) :
    compInv f g B n x = x := sorry

/-- The forward comparison followed by the inverse is the identity. -/
@[simp]
theorem compHom_compInv (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    compHom f g B ≫ compInv f g B = 𝟙 (B.restrictScalars (g.comp f)) := sorry

/-- The inverse comparison followed by the forward comparison is the identity. -/
@[simp]
theorem compInv_compHom (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    compInv f g B ≫ compHom f g B =
      𝟙 ((B.restrictScalars g).restrictScalars f) := sorry

/-- The canonical chain-DGA isomorphism from direct restriction along `g.comp f` to successive
restriction along `g` and then `f`. -/
@[stacks 09PQ "composition of restriction of scalars for chain DGAs"]
def compIso (f : R →+* S) (g : S →+* T) (B : ChainDGAlgebra.{uT, uB} T) :
    B.restrictScalars (g.comp f) ≅ (B.restrictScalars g).restrictScalars f where
  hom := compHom f g B
  inv := compInv f g B
  hom_inv_id := compHom_compInv f g B
  inv_hom_id := compInv_compHom f g B

/-- The forward morphism of the composition isomorphism is the explicit forward comparison. -/
@[simp]
theorem compIso_hom (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    (compIso f g B).hom = compHom f g B := sorry

/-- The inverse morphism of the composition isomorphism is the explicit inverse comparison. -/
@[simp]
theorem compIso_inv (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) :
    (compIso f g B).inv = compInv f g B := sorry

/-- The forward morphism of the composition isomorphism acts as the identity in every degree. -/
@[simp]
theorem compIso_hom_apply (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (n : ℤ)
    (x : (B.restrictScalars (g.comp f)).X n) :
    (compIso f g B).hom n x = x := sorry

/-- The inverse morphism of the composition isomorphism acts as the identity in every degree. -/
@[simp]
theorem compIso_inv_apply (f : R →+* S) (g : S →+* T)
    (B : ChainDGAlgebra.{uT, uB} T) (n : ℤ)
    (x : ((B.restrictScalars g).restrictScalars f).X n) :
    (compIso f g B).inv n x = x := sorry

/-- The forward composition comparison is natural in chain-DGA morphisms. -/
theorem compIso_hom_naturality (f : R →+* S) (g : S →+* T)
    {B C : ChainDGAlgebra.{uT, uB} T} (phi : B ⟶ C) :
    map (g.comp f) phi ≫ (compIso f g C).hom =
      (compIso f g B).hom ≫ map f (map g phi) := sorry

/-- The inverse composition comparison is natural in chain-DGA morphisms. -/
theorem compIso_inv_naturality (f : R →+* S) (g : S →+* T)
    {B C : ChainDGAlgebra.{uT, uB} T} (phi : B ⟶ C) :
    map f (map g phi) ≫ (compIso f g C).inv =
      (compIso f g B).inv ≫ map (g.comp f) phi := sorry

end Composition

section Coherence

variable {R : Type uR} {S : Type uS} {T : Type uT} {U : Type uU}
  [CommRing R] [CommRing S] [CommRing T] [CommRing U]

/-- The two forward composition comparisons for three successive restrictions agree. -/
theorem compIso_hom_assoc (f : R →+* S) (g : S →+* T) (h : T →+* U)
    (B : ChainDGAlgebra.{uU, uB} U) :
    (compIso f (h.comp g) B).hom ≫ map f (compIso g h B).hom =
      (compIso (g.comp f) h B).hom ≫
        (compIso f g (B.restrictScalars h)).hom := sorry

/-- The two inverse composition comparisons for three successive restrictions agree. -/
theorem compIso_inv_assoc (f : R →+* S) (g : S →+* T) (h : T →+* U)
    (B : ChainDGAlgebra.{uU, uB} U) :
    map f (compIso g h B).inv ≫ (compIso f (h.comp g) B).inv =
      (compIso f g (B.restrictScalars h)).inv ≫
        (compIso (g.comp f) h B).inv := sorry

end Coherence

end ChainDGAlgebra.RestrictScalars
