/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Galois.IntegralClosure.InertiaDiagram
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.InertiaDiagram
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.FunctionFieldExtension
open CategoryTheory EtaleFundamentalGroup Ideal InfiniteGalois IsLocalRing
open integralClosure

universe u

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
variable [IsIntegral (Spec (CommRingCat.of A))]
variable [IsIntegrallyClosed A]
variable (hX : (Spec (CommRingCat.of A)).isNormal)
variable (m : Ideal
    (integralClosure A (SeparableClosure (Spec (CommRingCat.of A)).functionField)))
  [m.IsMaximal] [m.LiesOver (maximalIdeal A)]

/- Lemma 58.13.1 -/
@[stacks 0BSW]
#check (AlgebraicGeometry.Scheme.galoisInertiaDiagram_pi1 (A := A) hX (m := m) :
  ∀ {Ah Ash : Type u} [CommRing Ah] [CommRing Ash]
    [Algebra A Ah] [Algebra A Ash] [Algebra Ah Ash]
    [IsHenselizationOf A Ah] [IsStrictHenselizationOf Ah Ash]
    [IsScalarTower A Ah Ash] [IsDomain Ah] [IsDomain Ash]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ush : Spec (.of Ω) ⟶ Spec (.of (FractionRing Ash)))
    (uh : Spec (.of Ω) ⟶ Spec (.of (FractionRing Ah)))
    (u : Spec (.of Ω) ⟶ Spec (.of (FractionRing A)))
    (xh : Spec (.of Ω) ⟶ Spec (.of Ah))
    (x : Spec (.of Ω) ⟶ Spec (.of A))
    (h_ush_uh : ush ≫
        Spec.map (CommRingCat.ofHom
          (IsFractionRing.map (K := FractionRing Ah) (L := FractionRing Ash)
            (j := algebraMap Ah Ash)
            (RingHom.FaithfullyFlat.injective
              (IsStrictHenselizationOf.faithfullyFlat (R := Ah) (S := Ash))))) = uh)
    (h_uh_u : uh ≫
        Spec.map (CommRingCat.ofHom
          (IsFractionRing.map (K := FractionRing A) (L := FractionRing Ah)
            (j := algebraMap A Ah)
            (RingHom.FaithfullyFlat.injective
              (IsHenselizationOf.faithfullyFlat (R := A) (S := Ah))))) = u)
    (h_uh_xh : uh ≫ Spec.map (CommRingCat.ofHom (algebraMap Ah (FractionRing Ah))) = xh)
    (h_u_x : u ≫ Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) = x)
    (h_triangle : ush ≫
        Spec.map (CommRingCat.ofHom (algebraMap Ah (FractionRing Ash))) = xh)
    (h_square : u ≫ Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) =
      xh ≫ Spec.map (CommRingCat.ofHom (algebraMap A Ah))),
    ∃ (eUsh : fundamentalGroup ush ≃ₜ* (integralClosure.inertiaProfinite
        (Spec (CommRingCat.of A)).functionField m))
      (eUh : fundamentalGroup uh ≃ₜ* (integralClosure.decompositionProfinite
        (Spec (CommRingCat.of A)).functionField m))
      (eU : fundamentalGroup u ≃ₜ* (profiniteGalGrp
        (Spec (CommRingCat.of A)).functionField
        (SeparableClosure (Spec (CommRingCat.of A)).functionField)))
      (eXh : fundamentalGroup xh ≃ₜ* (profiniteGalGrp
        (maximalIdeal A).ResidueField
        (separableClosure (maximalIdeal A).ResidueField
          m.ResidueField)))
      (eX : fundamentalGroup x ≃ₜ* (profiniteGalGrp
        (Spec (CommRingCat.of A)).functionField
        (maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX))) ,
      (∀ g, eUh ((h_ush_uh ▸
          Hom.fundamentalGroupMap
            (Spec.map (CommRingCat.ofHom
              (IsFractionRing.map (K := FractionRing Ah) (L := FractionRing Ash)
                (j := algebraMap Ah Ash)
                (RingHom.FaithfullyFlat.injective
                  (IsStrictHenselizationOf.faithfullyFlat (R := Ah) (S := Ash)))))) ush) g) =
        (EtaleFundamentalGroup.galoisInertiaDiagram hX m).ushToUh (eUsh g)) ∧
      (∀ g, eU ((h_uh_u ▸
          Hom.fundamentalGroupMap
            (Spec.map (CommRingCat.ofHom
              (IsFractionRing.map (K := FractionRing A) (L := FractionRing Ah)
                (j := algebraMap A Ah)
                (RingHom.FaithfullyFlat.injective
                  (IsHenselizationOf.faithfullyFlat (R := A) (S := Ah)))))) uh) g) =
        (EtaleFundamentalGroup.galoisInertiaDiagram hX m).uhToU (eUh g)) ∧
      (∀ g, eXh ((h_uh_xh ▸
          Hom.fundamentalGroupMap
            (Spec.map (CommRingCat.ofHom (algebraMap Ah (FractionRing Ah)))) uh) g) =
        (EtaleFundamentalGroup.galoisInertiaDiagram hX m).uhToXh (eUh g)) ∧
      (∀ g, eX ((h_u_x ▸
          Hom.fundamentalGroupMap
            (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) u) g) =
        (EtaleFundamentalGroup.galoisInertiaDiagram hX m).uToX (eU g)) ∧
      (∀ g, eXh ((h_triangle ▸
          Hom.fundamentalGroupMap
            (Spec.map (CommRingCat.ofHom (algebraMap Ah (FractionRing Ash)))) ush) g) =
        (EtaleFundamentalGroup.galoisInertiaDiagram hX m).ushToXh (eUsh g)) ∧
      (∀ g, eX ((h_square.symm.trans h_u_x ▸
          Hom.fundamentalGroupMap
            (Spec.map (CommRingCat.ofHom (algebraMap A Ah))) xh) g) =
        (EtaleFundamentalGroup.galoisInertiaDiagram hX m).xhToX (eXh g)))

#check (integralClosure.residueGaloisHom_surjective (A := A) m :
  Function.Surjective
    (integralClosure.residueGaloisHom (Spec (CommRingCat.of A)).functionField m))
#check (AlgEquiv.restrictNormalHom_surjective
    (F := (Spec (CommRingCat.of A)).functionField)
    (K₁ := maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX)
    (SeparableClosure (Spec (CommRingCat.of A)).functionField) :
  Function.Surjective
    (AlgEquiv.restrictNormalHom
      (maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX)))
#check integralClosure.residueGaloisHom_ker (A := A) m
#check (EtaleFundamentalGroup.restrictUnramifiedHom_ker (A := A) hX m :
  (EtaleFundamentalGroup.restrictUnramifiedHom
      (Spec (CommRingCat.of A)).functionField
      (maximalUnramifiedExtension (Spec (CommRingCat.of A)) hX)).ker =
    (Subgroup.normalClosure
      (m.inertia
          (SeparableClosure (Spec (CommRingCat.of A)).functionField ≃ₐ[
            (Spec (CommRingCat.of A)).functionField]
            SeparableClosure (Spec (CommRingCat.of A)).functionField) :
        Set
          (SeparableClosure (Spec (CommRingCat.of A)).functionField ≃ₐ[
            (Spec (CommRingCat.of A)).functionField]
            SeparableClosure (Spec (CommRingCat.of A)).functionField))).topologicalClosure)
#check EtaleFundamentalGroup.galoisInertiaDiagram (A := A) hX m
