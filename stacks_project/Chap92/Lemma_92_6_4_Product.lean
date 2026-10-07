module

public import stacks_project.Chap92.Lemma_92_3_4_DirectLimit
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.HomologicalComplex.Restriction
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory

/-!
# Product comparison of André-Quillen cotangent complexes

For ring maps `A → B` and `A → C`, this module owns the canonical comparison
`L_{B × C / A} ⟶ L_{B/A} ⊕ L_{C/A}` in `D(B × C)`, obtained by adjoining the
two functoriality maps along `RingHom.fst` and `RingHom.snd` and assembling them
by `biprod.lift`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open ComplexShape

noncomputable section

universe u

namespace Algebra.CotangentComplex

/-- Commutativity of the identity-on-`A` square with right vertical map `RingHom.fst`. -/
theorem prod_fst_comm {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    f.comp (RingHom.id A) = (RingHom.fst B C).comp (f.prod g) :=
  sorry

/-- Commutativity of the identity-on-`A` square with right vertical map `RingHom.snd`. -/
theorem prod_snd_comm {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    g.comp (RingHom.id A) = (RingHom.snd B C).comp (f.prod g) :=
  sorry

/-- `L_{B/A}` viewed in cochain complexes of `B × C`-modules by restriction along `RingHom.fst`. -/
abbrev prodRestrictLeft {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) :
    CochainComplex (ModuleCat.{u} (B × C)) ℤ :=
  (RingHom.cotangentComplex f).restrictScalarsAlong (RingHom.fst B C)

/-- Unfolding of `prodRestrictLeft` as restriction of scalars along `RingHom.fst`. -/
theorem prodRestrictLeft_eq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) :
    prodRestrictLeft f =
      (RingHom.cotangentComplex f).restrictScalarsAlong (RingHom.fst B C) :=
  sorry

/-- `L_{C/A}` viewed in cochain complexes of `B × C`-modules by restriction along `RingHom.snd`. -/
abbrev prodRestrictRight {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* C) :
    CochainComplex (ModuleCat.{u} (B × C)) ℤ :=
  (RingHom.cotangentComplex g).restrictScalarsAlong (RingHom.snd B C)

/-- Unfolding of `prodRestrictRight` as restriction of scalars along `RingHom.snd`. -/
theorem prodRestrictRight_eq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* C) :
    prodRestrictRight g =
      (RingHom.cotangentComplex g).restrictScalarsAlong (RingHom.snd B C) :=
  sorry

/-- Functoriality map of cotangent complexes after extending scalars along `RingHom.fst`. -/
def prodMapLeftExtend {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    ((ModuleCat.extendScalars (RingHom.fst B C)).mapHomologicalComplex (up ℤ)).obj
        (RingHom.cotangentComplex (f.prod g)) ⟶
      RingHom.cotangentComplex f :=
  map (f.prod g) f (RingHom.id A) (RingHom.fst B C)
    ((RingHom.comp_id f).trans (RingHom.fst_comp_prod f g).symm)

/-- Unfolding of `prodMapLeftExtend` as `Algebra.CotangentComplex.map` along `RingHom.fst`. -/
theorem prodMapLeftExtend_eq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    prodMapLeftExtend f g =
      map (f.prod g) f (RingHom.id A) (RingHom.fst B C)
        ((RingHom.comp_id f).trans (RingHom.fst_comp_prod f g).symm) :=
  sorry

/-- Functoriality map of cotangent complexes after extending scalars along `RingHom.snd`. -/
def prodMapRightExtend {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    ((ModuleCat.extendScalars (RingHom.snd B C)).mapHomologicalComplex (up ℤ)).obj
        (RingHom.cotangentComplex (f.prod g)) ⟶
      RingHom.cotangentComplex g :=
  map (f.prod g) g (RingHom.id A) (RingHom.snd B C)
    ((RingHom.comp_id g).trans (RingHom.snd_comp_prod f g).symm)

/-- Unfolding of `prodMapRightExtend` as `Algebra.CotangentComplex.map` along `RingHom.snd`. -/
theorem prodMapRightExtend_eq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    prodMapRightExtend f g =
      map (f.prod g) g (RingHom.id A) (RingHom.snd B C)
        ((RingHom.comp_id g).trans (RingHom.snd_comp_prod f g).symm) :=
  sorry

/-- Left component of the product comparison, as the adjunct of `prodMapLeftExtend`. -/
def prodMapLeftCochain {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    RingHom.cotangentComplex (f.prod g) ⟶ prodRestrictLeft f :=
  (Adjunction.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (RingHom.fst B C)) (up ℤ)).homEquiv
    (RingHom.cotangentComplex (f.prod g)) (RingHom.cotangentComplex f) (prodMapLeftExtend f g)

/-- Right component of the product comparison, as the adjunct of `prodMapRightExtend`. -/
def prodMapRightCochain {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    RingHom.cotangentComplex (f.prod g) ⟶ prodRestrictRight g :=
  (Adjunction.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (RingHom.snd B C)) (up ℤ)).homEquiv
    (RingHom.cotangentComplex (f.prod g)) (RingHom.cotangentComplex g) (prodMapRightExtend f g)

/-- Canonical cochain-level product comparison
`L_{B × C / A} ⟶ L_{B/A} ⊕ L_{C/A}` over `B × C`. -/
def prodMapCochain {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    RingHom.cotangentComplex (f.prod g) ⟶ prodRestrictLeft f ⊞ prodRestrictRight g :=
  biprod.lift (prodMapLeftCochain f g) (prodMapRightCochain f g)

/-- Unfolding of `prodMapCochain` as `biprod.lift` of the two adjuncts. -/
theorem prodMapCochain_eq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    prodMapCochain f g = biprod.lift (prodMapLeftCochain f g) (prodMapRightCochain f g) :=
  sorry

/-- The first projection recovers the left adjunct. -/
theorem prodMapCochain_fst {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    prodMapCochain f g ≫ biprod.fst = prodMapLeftCochain f g :=
  sorry

/-- The second projection recovers the right adjunct. -/
theorem prodMapCochain_snd {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    prodMapCochain f g ≫ biprod.snd = prodMapRightCochain f g :=
  sorry

/-- Canonical derived product comparison
`L_{B × C / A} ⟶ L_{B/A} ⊕ L_{C/A}` in `D(B × C)`. -/
def prodMap {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    DerivedCategory.Q.obj (RingHom.cotangentComplex (f.prod g)) ⟶
      DerivedCategory.Q.obj (prodRestrictLeft f ⊞ prodRestrictRight g) :=
  DerivedCategory.Q.map (prodMapCochain f g)

/-- Unfolding of `prodMap` as `DerivedCategory.Q.map` of `prodMapCochain`. -/
theorem prodMap_eq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    prodMap f g = DerivedCategory.Q.map (prodMapCochain f g) :=
  sorry

/-- Algebra-form of `prodMapCochain` for `A`-algebras `B` and `C`. -/
abbrev prodMapCochain_algebra (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] :=
  prodMapCochain (algebraMap A B) (algebraMap A C)

/-- Unfolding of `prodMapCochain_algebra` as `prodMapCochain` of the structure maps. -/
theorem prodMapCochain_algebra_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] :
    prodMapCochain_algebra A B C = prodMapCochain (algebraMap A B) (algebraMap A C) :=
  sorry

/-- Algebra-form of `prodMap` for `A`-algebras `B` and `C`. -/
abbrev prodMap_algebra (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] :=
  prodMap (algebraMap A B) (algebraMap A C)

/-- Unfolding of `prodMap_algebra` as `prodMap` of the structure maps. -/
theorem prodMap_algebra_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] :
    prodMap_algebra A B C = prodMap (algebraMap A B) (algebraMap A C) :=
  sorry

end Algebra.CotangentComplex
