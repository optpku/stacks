module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Over
public import ReasLib.RingTheory.AdicAlgebraSystem

/-!
# Adic quotient systems of algebras

The quotient rings `B ⧸ I ^ n B` form a positive inverse system over the
adic quotient system of the base ring, functorially in the algebra `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.PNatInverseSystem

noncomputable section

universe u

namespace CommAlgCat

variable {A : Type u} [CommRing A]

/-- The quotient of an `A`-algebra by the extension of the positive power `I ^ n`. -/
abbrev adicQuotientStage (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] (n : ℕ+) :
    CommRingCat.{u} :=
  CommRingCat.of (B ⧸ (I ^ (n : ℕ)).map (algebraMap A B))

/-- The quotient-factor map of an identity index is the identity of the quotient algebra. -/
theorem adicQuotientSystem_map_id (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    (i : OrderDual ℕ+) :
    CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.map_mono (AdicAlgebraSystem.pow_le_of_orderDual_hom I (𝟙 i)))) =
      𝟙 (adicQuotientStage I B (OrderDual.ofDual i)) := sorry

/-- Quotient-factor maps of extended ideal powers compose along order-dual indices. -/
theorem adicQuotientSystem_map_comp (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    {i j k : OrderDual ℕ+} (f : i ⟶ j) (g : j ⟶ k) :
    CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.map_mono (f := algebraMap A B)
        (AdicAlgebraSystem.pow_le_of_orderDual_hom I (f ≫ g)))) =
      CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.map_mono (f := algebraMap A B)
          (AdicAlgebraSystem.pow_le_of_orderDual_hom I f))) ≫
        CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.map_mono (f := algebraMap A B)
            (AdicAlgebraSystem.pow_le_of_orderDual_hom I g))) := sorry

/-- The positive inverse system of quotients of `B` by the extended powers of `I`. -/
def adicQuotientSystem (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] :
    PNatInverseSystem CommRingCat.{u} where
  obj i := adicQuotientStage I B (OrderDual.ofDual i)
  map f := CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.map_mono (AdicAlgebraSystem.pow_le_of_orderDual_hom I f)))
  map_id := adicQuotientSystem_map_id I B
  map_comp := adicQuotientSystem_map_comp I B

/-- The stage at `n` of the adic quotient system is the quotient by the extension of `I ^ n`. -/
theorem adicQuotientSystem_stage (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] (n : ℕ+) :
    (adicQuotientSystem I B).stage n = adicQuotientStage I B n := sorry

/-- An `A`-algebra homomorphism induces a ring homomorphism on quotients by extended powers. -/
def adicQuotientMap {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (I : Ideal A) (f : B →ₐ[A] C) (n : ℕ+) :
    B ⧸ (I ^ (n : ℕ)).map (algebraMap A B) →+* C ⧸ (I ^ (n : ℕ)).map (algebraMap A C) :=
  Ideal.quotientMap ((I ^ (n : ℕ)).map (algebraMap A C)) f.toRingHom
    (Ideal.map_le_iff_le_comap.mp (le_of_eq
      ((Ideal.map_map (algebraMap A B) f.toRingHom).trans
        (congrArg (fun hom ↦ (I ^ (n : ℕ)).map hom) f.comp_algebraMap))))

/-- The map on adic quotients sends the class of an element to the class of its image. -/
theorem adicQuotientMap_mk {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (I : Ideal A) (f : B →ₐ[A] C) (n : ℕ+) (element : B) :
    adicQuotientMap I f n (Ideal.Quotient.mk _ element) =
      Ideal.Quotient.mk _ (f element) := sorry

/-- Maps induced by an algebra homomorphism commute with quotient-system transitions. -/
theorem adicQuotientSystemMap_naturality {B C : Type u} [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (I : Ideal A) (f : B →ₐ[A] C)
    {i j : OrderDual ℕ+} (transition : i ⟶ j) :
    (adicQuotientSystem I B).map transition ≫
        CommRingCat.ofHom (adicQuotientMap I f (OrderDual.ofDual j)) =
      CommRingCat.ofHom (adicQuotientMap I f (OrderDual.ofDual i)) ≫
        (adicQuotientSystem I C).map transition := sorry

/-- The natural transformation on adic quotient systems induced by an algebra homomorphism. -/
def adicQuotientSystemMap {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (I : Ideal A) (f : B →ₐ[A] C) :
    adicQuotientSystem I B ⟶ adicQuotientSystem I C where
  app i := CommRingCat.ofHom (adicQuotientMap I f (OrderDual.ofDual i))
  naturality := fun {_ _} transition ↦ adicQuotientSystemMap_naturality I f transition

/-- Components of the induced natural transformation are the induced quotient maps. -/
theorem adicQuotientSystemMap_app {B C : Type u} [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (I : Ideal A) (f : B →ₐ[A] C) (n : ℕ+) :
    (adicQuotientSystemMap I f).app (OrderDual.toDual n) =
      CommRingCat.ofHom (adicQuotientMap I f n) := sorry

/-- Quotient structure maps induced by `algebraMap` commute with the transition maps. -/
theorem adicQuotientStructure_naturality (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    {i j : OrderDual ℕ+} (transition : i ⟶ j) :
    (AdicAlgebraSystem.quotientSystem I).map transition ≫
        CommRingCat.ofHom (Ideal.quotientMap
          ((I ^ ((OrderDual.ofDual j : ℕ+) : ℕ)).map (algebraMap A B))
          (algebraMap A B) Ideal.le_comap_map) =
      CommRingCat.ofHom (Ideal.quotientMap
        ((I ^ ((OrderDual.ofDual i : ℕ+) : ℕ)).map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map) ≫
          (adicQuotientSystem I B).map transition := sorry

/-- The natural transformation from the base quotient tower induced by the algebra structure. -/
def adicQuotientStructure (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] :
    AdicAlgebraSystem.quotientSystem I ⟶ adicQuotientSystem I B where
  app i := CommRingCat.ofHom (Ideal.quotientMap
    ((I ^ ((OrderDual.ofDual i : ℕ+) : ℕ)).map (algebraMap A B))
    (algebraMap A B) Ideal.le_comap_map)
  naturality := fun {_ _} transition ↦ adicQuotientStructure_naturality I B transition

/-- The quotient system of an algebra as an object under the adic quotient tower of its base. -/
def adicQuotientUnder (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] :
    Under (AdicAlgebraSystem.quotientSystem I) :=
  Under.mk (adicQuotientStructure I B)

/-- Stages of the quotient under-object are quotients by the extended powers of the ideal. -/
theorem adicQuotientUnder_stage (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] (n : ℕ+) :
    (adicQuotientUnder I B).right.stage n = adicQuotientStage I B n := sorry

/-- The induced natural transformation on quotient systems commutes with the base structure. -/
theorem adicQuotientUnderMap_w {B C : Type u} [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (I : Ideal A) (f : B →ₐ[A] C) :
    adicQuotientStructure I B ≫ adicQuotientSystemMap I f =
      adicQuotientStructure I C := sorry

/-- An algebra homomorphism induces a morphism of quotient systems over the base tower. -/
def adicQuotientUnderMap {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (I : Ideal A) (f : B →ₐ[A] C) :
    adicQuotientUnder I B ⟶ adicQuotientUnder I C :=
  Under.homMk (adicQuotientSystemMap I f) (adicQuotientUnderMap_w I f)

/-- Finite type of the special fiber implies finite type of every positive adic quotient. -/
instance finiteType_quotientStage (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))] (n : ℕ+) :
    Algebra.FiniteType (A ⧸ I ^ (n : ℕ)) (B ⧸ (I ^ (n : ℕ)).map (algebraMap A B)) := sorry

/-- The stage structure maps of an algebra with finite-type special fiber are of finite type. -/
theorem finiteType_stageAlgebraMap (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))] (n : ℕ+) :
    (AdicAlgebraSystem.stageAlgebraMap I (adicQuotientUnder I B) n).FiniteType := sorry

/-- An algebra with finite-type special fiber has a finite-type adic quotient system. -/
instance instIsObjectAdicQuotientUnder (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))] :
    AdicAlgebraSystem.IsObject I (adicQuotientUnder I B) := sorry

end CommAlgCat
