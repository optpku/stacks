module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import stacks_project.Chap98.Lemma_98_9_3_FormalObject

/-!
# Morphisms of complete local `S`-algebras

A morphism of complete local `S`-algebras is a local ring homomorphism
compatible with the structure morphisms to `S`. The induced map on
spectra is the source morphism `a0 : Spec R ⟶ Spec T`, and truncations
yield `Spec(R ⧸ m^{n+1}) ⟶ Spec(T ⧸ m^{n+1})` in `Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.CompleteLocalSAlgebra

variable {S : Scheme.{u}}

/-- A morphism of complete local `S`-algebras is a local ring map
`T →+* R` whose spectrum is a morphism `Spec R ⟶ Spec T` over `S`. -/
structure Hom (R T : CompleteLocalSAlgebra S) where
  /-- Underlying local ring homomorphism, dual to `Spec R ⟶ Spec T`. -/
  hom : T.carrier →+* R.carrier
  [isLocalHom : IsLocalHom hom]
  /-- The spectrum of `hom` lies over `S`. -/
  over_S : Spec.map (CommRingCat.ofHom hom) ≫ T.toS = R.toS

attribute [instance] Hom.isLocalHom

/-- Package a local ring homomorphism over `S` as a morphism of complete local
`S`-algebras. -/
def Hom.of {R T : CompleteLocalSAlgebra S} (hom : T.carrier →+* R.carrier)
    [IsLocalHom hom]
    (over_S : Spec.map (CommRingCat.ofHom hom) ≫ T.toS = R.toS) :
    Hom R T where
  hom := hom
  over_S := over_S

/-- Identity morphism of a complete local `S`-algebra. -/
def Hom.id (R : CompleteLocalSAlgebra S) : Hom R R where
  hom := RingHom.id R.carrier
  over_S := sorry

/-- Composition of morphisms of complete local `S`-algebras, covariant for
`Spec` and contravariant for the underlying ring maps. -/
def Hom.comp {R T Q : CompleteLocalSAlgebra S} (f : Hom R T) (g : Hom T Q) :
    Hom R Q where
  hom := f.hom.comp g.hom
  over_S := sorry

/-- The identity morphism is the identity ring map. -/
theorem Hom.id_hom (R : CompleteLocalSAlgebra S) :
    (Hom.id R).hom = RingHom.id R.carrier := sorry

/-- Composition of morphisms is composition of the underlying ring maps. -/
theorem Hom.comp_hom {R T Q : CompleteLocalSAlgebra S} (f : Hom R T)
    (g : Hom T Q) : (Hom.comp f g).hom = f.hom.comp g.hom := sorry

/-- Morphisms are local ring maps whose spectra lie over `S`. -/
theorem Hom.spec {R T : CompleteLocalSAlgebra S} (f : Hom R T) :
    IsLocalHom f.hom ∧ Spec.map (CommRingCat.ofHom f.hom) ≫ T.toS = R.toS :=
  sorry

/-- The induced scheme morphism `a0 : Spec R ⟶ Spec T`. -/
def Hom.toSpec {R T : CompleteLocalSAlgebra S} (f : Hom R T) :
    Spec (CommRingCat.of R.carrier) ⟶ Spec (CommRingCat.of T.carrier) :=
  Spec.map (CommRingCat.ofHom f.hom)

/-- `toSpec` is the spectrum of the underlying ring homomorphism. -/
theorem Hom.toSpec_eq {R T : CompleteLocalSAlgebra S} (f : Hom R T) :
    f.toSpec = Spec.map (CommRingCat.ofHom f.hom) := sorry

/-- The spectrum of a morphism of complete local `S`-algebras lies over `S`. -/
theorem Hom.toSpec_comp_toS {R T : CompleteLocalSAlgebra S} (f : Hom R T) :
    f.toSpec ≫ T.toS = R.toS := sorry

/-- Induced map of maximal-adic truncations `T ⧸ m^{n+1} →+* R ⧸ m^{n+1}`. -/
def Hom.stageRingHom {R T : CompleteLocalSAlgebra S} (f : Hom R T) (n : ℕ) :
    T.truncationRing n ⟶ R.truncationRing n :=
  CommRingCat.ofHom
    (Ideal.quotientMap (maximalIdeal R.carrier ^ (n + 1)) f.hom
      (maximalIdeal_comap f.hom ▸
        (Ideal.le_comap_pow f.hom (n + 1) :
          (maximalIdeal R.carrier).comap f.hom ^ (n + 1) ≤
            (maximalIdeal R.carrier ^ (n + 1)).comap f.hom)))

/-- Truncated spectra of a morphism of complete local `S`-algebras commute with
the structure maps to `S`. -/
theorem Hom.stageToS_comp {R T : CompleteLocalSAlgebra S} (f : Hom R T) (n : ℕ) :
    Spec.map (f.stageRingHom n) ≫ T.truncationToS n = R.truncationToS n :=
  sorry

/-- Induced morphism `Spec(R ⧸ m^{n+1}) ⟶ Spec(T ⧸ m^{n+1})` in `Over S`. -/
def Hom.stageMap {R T : CompleteLocalSAlgebra S} (f : Hom R T) (n : ℕ) :
    R.stageOver n ⟶ T.stageOver n :=
  Over.homMk (Spec.map (f.stageRingHom n)) (f.stageToS_comp n)

/-- The underlying scheme morphism of a truncated stage map is the spectrum of
the truncated ring map. -/
theorem Hom.stageMap_left {R T : CompleteLocalSAlgebra S} (f : Hom R T) (n : ℕ) :
    (f.stageMap n).left = Spec.map (f.stageRingHom n) := sorry

end AlgebraicGeometry.CompleteLocalSAlgebra
