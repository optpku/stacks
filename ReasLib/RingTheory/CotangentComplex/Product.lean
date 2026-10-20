module

public import ReasLib.RingTheory.CotangentComplex.Functoriality
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

For ring maps `A → B` and `A → C`, the canonical comparison
`L_{B × C / A} ⟶ L_{B/A} ⊕ L_{C/A}` in `D(B × C)` is obtained from the
two functoriality maps along the product projections.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open ComplexShape

noncomputable section

universe u

namespace Algebra.CotangentComplex

/-- `L_{B/A}` viewed as a cochain complex of `B × C`-modules by restriction
along the first projection. -/
abbrev prodRestrictLeft {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) :
    CochainComplex (ModuleCat.{u} (B × C)) ℤ :=
  (RingHom.cotangentComplex f).restrictScalarsAlong (RingHom.fst B C)

/-- `L_{C/A}` viewed as a cochain complex of `B × C`-modules by restriction
along the second projection. -/
abbrev prodRestrictRight {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* C) :
    CochainComplex (ModuleCat.{u} (B × C)) ℤ :=
  (RingHom.cotangentComplex g).restrictScalarsAlong (RingHom.snd B C)

/-- The functoriality map of cotangent complexes after extending scalars
along the first product projection. -/
def prodMapLeftExtend {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    ((ModuleCat.extendScalars (RingHom.fst B C)).mapHomologicalComplex (up ℤ)).obj
        (RingHom.cotangentComplex (f.prod g)) ⟶
      RingHom.cotangentComplex f :=
  map (f.prod g) f (RingHom.id A) (RingHom.fst B C)
    ((RingHom.comp_id f).trans (RingHom.fst_comp_prod f g).symm)

/-- The functoriality map of cotangent complexes after extending scalars
along the second product projection. -/
def prodMapRightExtend {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    ((ModuleCat.extendScalars (RingHom.snd B C)).mapHomologicalComplex (up ℤ)).obj
        (RingHom.cotangentComplex (f.prod g)) ⟶
      RingHom.cotangentComplex g :=
  map (f.prod g) g (RingHom.id A) (RingHom.snd B C)
    ((RingHom.comp_id g).trans (RingHom.snd_comp_prod f g).symm)

/-- The left component of the product comparison is the adjunct of the
scalar-extended functoriality map along the first projection. -/
def prodMapLeftCochain {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    RingHom.cotangentComplex (f.prod g) ⟶ prodRestrictLeft f :=
  (Adjunction.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (RingHom.fst B C)) (up ℤ)).homEquiv
    (RingHom.cotangentComplex (f.prod g)) (RingHom.cotangentComplex f) (prodMapLeftExtend f g)

/-- The right component of the product comparison is the adjunct of the
scalar-extended functoriality map along the second projection. -/
def prodMapRightCochain {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    RingHom.cotangentComplex (f.prod g) ⟶ prodRestrictRight g :=
  (Adjunction.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (RingHom.snd B C)) (up ℤ)).homEquiv
    (RingHom.cotangentComplex (f.prod g)) (RingHom.cotangentComplex g) (prodMapRightExtend f g)

/-- The canonical cochain-level product comparison
`L_{B × C / A} ⟶ L_{B/A} ⊕ L_{C/A}` over `B × C`. -/
def prodMapCochain {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    RingHom.cotangentComplex (f.prod g) ⟶ prodRestrictLeft f ⊞ prodRestrictRight g :=
  biprod.lift (prodMapLeftCochain f g) (prodMapRightCochain f g)

/-- The first projection of the product comparison is its left component. -/
theorem prodMapCochain_fst {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    prodMapCochain f g ≫ biprod.fst = prodMapLeftCochain f g :=
  biprod.lift_fst (prodMapLeftCochain f g) (prodMapRightCochain f g)

/-- The second projection of the product comparison is its right component. -/
theorem prodMapCochain_snd {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    prodMapCochain f g ≫ biprod.snd = prodMapRightCochain f g :=
  biprod.lift_snd (prodMapLeftCochain f g) (prodMapRightCochain f g)

/-- The canonical derived product comparison
`L_{B × C / A} ⟶ L_{B/A} ⊕ L_{C/A}` in `D(B × C)`. -/
def prodMap {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) :
    DerivedCategory.Q.{u + 1}.obj (RingHom.cotangentComplex (f.prod g)) ⟶
      DerivedCategory.Q.{u + 1}.obj (prodRestrictLeft f ⊞ prodRestrictRight g) :=
  DerivedCategory.Q.{u + 1}.map (prodMapCochain f g)

/-- The canonical comparison from the cotangent complex of a product to the
direct sum of the factor cotangent complexes is an isomorphism in `D(B × C)`. -/
instance prodMap_isIso {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) : IsIso (prodMap f g) :=
  sorry

end Algebra.CotangentComplex
