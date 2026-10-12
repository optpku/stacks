/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap87.Lemma_87_9_10_Map
public import stacks_project.Chap87.Lemma_87_10_4_Predicates
public import stacks_project.Chap87.Situation_87_21_2_MorphismProperty

/-!
# WAdm^count correspondence for morphisms of affine formal algebraic spaces

A morphism of affine formal algebraic spaces over `S` corresponds to a morphism
of `WAdm^count` with property `P` when some countably indexed weakly admissible
presentations identify it with `Spf(φ)` for a continuous `S`-algebra map `φ`
satisfying `P`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

noncomputable section

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)

/-- A morphism of affine formal algebraic spaces corresponds to a morphism of
`WAdm^count` with property `P` when there are countably indexed weakly
admissible presentations of source and target, together with a continuous
`S`-algebra map `φ` satisfying `P`, such that `f` is identified with `Spf(φ)`
on weak-ideal stages. -/
def correspondsTo {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : U ⟶ V) : Prop :=
  ∃ (A B : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
    (_ : IsWeaklyAdmissibleRing A) (_ : IsCountablyIndexed A)
    (_ : CommRing B) (_ : TopologicalSpace B)
    (_ : IsWeaklyAdmissibleRing B) (_ : IsCountablyIndexed B)
    (hA : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
    (hB : Spec (.of B) ⟶ 𝒮.toScheme.obj S)
    (φ : B →+* A) (_ : Continuous φ)
    (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hB = hA)
    (DU : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
    (eU : ∀ I, (𝒮.bigAffineToScheme S).obj (DU.obj I) ≅ (stage A hA I).left)
    (cU : Cocone (DU ⋙ 𝒮.bigAffineInclusion S ⋙
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (iU : U ≅ cU.pt)
    (DV : WeakIdealOfDefinition B ⥤ 𝒮.bigAffineSite S)
    (eV : ∀ J, (𝒮.bigAffineToScheme S).obj (DV.obj J) ≅ (stage B hB J).left)
    (cV : Cocone (DV ⋙ 𝒮.bigAffineInclusion S ⋙
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (iV : V ≅ cV.pt),
    P φ ∧ Nonempty (IsColimit cU) ∧ Nonempty (IsColimit cV) ∧
      (∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
        (eU I).hom ≫ ((thickenings A hA).map g).left =
          (𝒮.bigAffineToScheme S).map (DU.map g) ≫ (eU J).hom) ∧
      (∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
        (eV I).hom ≫ ((thickenings B hB).map g).left =
          (𝒮.bigAffineToScheme S).map (DV.map g) ≫ (eV J).hom) ∧
      (∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
        IsThickening ((𝒮.bigAffineToScheme S).map (DU.map g))) ∧
      (∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
        IsThickening ((𝒮.bigAffineToScheme S).map (DV.map g))) ∧
      ∀ (I : WeakIdealOfDefinition A) (J : WeakIdealOfDefinition B)
        (hIJ : J.ideal ≤ Ideal.comap φ I.ideal),
        ∃ t : DU.obj I ⟶ DV.obj J,
          CommSq ((𝒮.bigAffineToScheme S).map t) (eU I).hom (eV J).hom
              (stageMap φ h_over hIJ).left ∧
            cU.ι.app I ≫ iU.inv ≫ f ≫ iV.hom =
              (𝒮.bigTopology S).sheafifiedRepresentableMap
                  ((𝒮.bigAffineInclusion S).map t) ≫ cV.ι.app J

/-- `correspondsTo P f` unpacks as countably indexed weakly admissible
presentations of the affine source and target together with a continuous
`S`-algebra map `φ` satisfying `P` that induces `f` on weak-ideal stages. -/
theorem correspondsTo_iff {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : U ⟶ V) :
    correspondsTo P f ↔
      ∃ (A B : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : IsWeaklyAdmissibleRing A) (_ : IsCountablyIndexed A)
        (_ : CommRing B) (_ : TopologicalSpace B)
        (_ : IsWeaklyAdmissibleRing B) (_ : IsCountablyIndexed B)
        (hA : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
        (hB : Spec (.of B) ⟶ 𝒮.toScheme.obj S)
        (φ : B →+* A) (_ : Continuous φ)
        (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hB = hA)
        (DU : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
        (eU : ∀ I, (𝒮.bigAffineToScheme S).obj (DU.obj I) ≅ (stage A hA I).left)
        (cU : Cocone (DU ⋙ 𝒮.bigAffineInclusion S ⋙
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
        (iU : U ≅ cU.pt)
        (DV : WeakIdealOfDefinition B ⥤ 𝒮.bigAffineSite S)
        (eV : ∀ J, (𝒮.bigAffineToScheme S).obj (DV.obj J) ≅ (stage B hB J).left)
        (cV : Cocone (DV ⋙ 𝒮.bigAffineInclusion S ⋙
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
        (iV : V ≅ cV.pt),
        P φ ∧ Nonempty (IsColimit cU) ∧ Nonempty (IsColimit cV) ∧
          (∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
            (eU I).hom ≫ ((thickenings A hA).map g).left =
              (𝒮.bigAffineToScheme S).map (DU.map g) ≫ (eU J).hom) ∧
          (∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
            (eV I).hom ≫ ((thickenings B hB).map g).left =
              (𝒮.bigAffineToScheme S).map (DV.map g) ≫ (eV J).hom) ∧
          (∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
            IsThickening ((𝒮.bigAffineToScheme S).map (DU.map g))) ∧
          (∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
            IsThickening ((𝒮.bigAffineToScheme S).map (DV.map g))) ∧
          ∀ (I : WeakIdealOfDefinition A) (J : WeakIdealOfDefinition B)
            (hIJ : J.ideal ≤ Ideal.comap φ I.ideal),
            ∃ t : DU.obj I ⟶ DV.obj J,
              CommSq ((𝒮.bigAffineToScheme S).map t) (eU I).hom (eV J).hom
                  (stageMap φ h_over hIJ).left ∧
                cU.ι.app I ≫ iU.inv ≫ f ≫ iV.hom =
                  (𝒮.bigTopology S).sheafifiedRepresentableMap
                      ((𝒮.bigAffineInclusion S).map t) ≫ cV.ι.app J :=
  sorry

namespace correspondsTo

variable {P}

/-- A continuous `S`-algebra map `φ` with `P φ`, together with compatible
`Spf` presentations of the affine source and target, witnesses
`correspondsTo P f`. -/
theorem of {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : U ⟶ V} {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
    (hA : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
    (hB : Spec (.of B) ⟶ 𝒮.toScheme.obj S)
    (φ : B →+* A) (hφ : Continuous φ)
    (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hB = hA)
    (hPφ : P φ)
    (DU : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
    (eU : ∀ I, (𝒮.bigAffineToScheme S).obj (DU.obj I) ≅ (stage A hA I).left)
    (cU : Cocone (DU ⋙ 𝒮.bigAffineInclusion S ⋙
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (iU : U ≅ cU.pt)
    (DV : WeakIdealOfDefinition B ⥤ 𝒮.bigAffineSite S)
    (eV : ∀ J, (𝒮.bigAffineToScheme S).obj (DV.obj J) ≅ (stage B hB J).left)
    (cV : Cocone (DV ⋙ 𝒮.bigAffineInclusion S ⋙
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (iV : V ≅ cV.pt)
    (hcU : Nonempty (IsColimit cU)) (hcV : Nonempty (IsColimit cV))
    (hDU : ∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
      (eU I).hom ≫ ((thickenings A hA).map g).left =
        (𝒮.bigAffineToScheme S).map (DU.map g) ≫ (eU J).hom)
    (hDV : ∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
      (eV I).hom ≫ ((thickenings B hB).map g).left =
        (𝒮.bigAffineToScheme S).map (DV.map g) ≫ (eV J).hom)
    (hThU : ∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
      IsThickening ((𝒮.bigAffineToScheme S).map (DU.map g)))
    (hThV : ∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
      IsThickening ((𝒮.bigAffineToScheme S).map (DV.map g)))
    (hMap : ∀ (I : WeakIdealOfDefinition A) (J : WeakIdealOfDefinition B)
      (hIJ : J.ideal ≤ Ideal.comap φ I.ideal),
      ∃ t : DU.obj I ⟶ DV.obj J,
        CommSq ((𝒮.bigAffineToScheme S).map t) (eU I).hom (eV J).hom
            (stageMap φ h_over hIJ).left ∧
          cU.ι.app I ≫ iU.inv ≫ f ≫ iV.hom =
            (𝒮.bigTopology S).sheafifiedRepresentableMap
                ((𝒮.bigAffineInclusion S).map t) ≫ cV.ι.app J) :
    correspondsTo P f := sorry

/-- `correspondsTo P f` supplies countably indexed weakly admissible
presentations and a continuous `S`-algebra map `φ` with `P φ` inducing `f`. -/
theorem spec {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : U ⟶ V} (h : correspondsTo P f) :
    ∃ (A B : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsWeaklyAdmissibleRing A) (_ : IsCountablyIndexed A)
      (_ : CommRing B) (_ : TopologicalSpace B)
      (_ : IsWeaklyAdmissibleRing B) (_ : IsCountablyIndexed B)
      (hA : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
      (hB : Spec (.of B) ⟶ 𝒮.toScheme.obj S)
      (φ : B →+* A) (_ : Continuous φ)
      (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hB = hA)
      (DU : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
      (eU : ∀ I, (𝒮.bigAffineToScheme S).obj (DU.obj I) ≅ (stage A hA I).left)
      (cU : Cocone (DU ⋙ 𝒮.bigAffineInclusion S ⋙
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
      (iU : U ≅ cU.pt)
      (DV : WeakIdealOfDefinition B ⥤ 𝒮.bigAffineSite S)
      (eV : ∀ J, (𝒮.bigAffineToScheme S).obj (DV.obj J) ≅ (stage B hB J).left)
      (cV : Cocone (DV ⋙ 𝒮.bigAffineInclusion S ⋙
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
      (iV : V ≅ cV.pt),
      P φ ∧ Nonempty (IsColimit cU) ∧ Nonempty (IsColimit cV) ∧
        (∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
          (eU I).hom ≫ ((thickenings A hA).map g).left =
            (𝒮.bigAffineToScheme S).map (DU.map g) ≫ (eU J).hom) ∧
        (∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
          (eV I).hom ≫ ((thickenings B hB).map g).left =
            (𝒮.bigAffineToScheme S).map (DV.map g) ≫ (eV J).hom) ∧
        (∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
          IsThickening ((𝒮.bigAffineToScheme S).map (DU.map g))) ∧
        (∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
          IsThickening ((𝒮.bigAffineToScheme S).map (DV.map g))) ∧
        ∀ (I : WeakIdealOfDefinition A) (J : WeakIdealOfDefinition B)
          (hIJ : J.ideal ≤ Ideal.comap φ I.ideal),
          ∃ t : DU.obj I ⟶ DV.obj J,
            CommSq ((𝒮.bigAffineToScheme S).map t) (eU I).hom (eV J).hom
                (stageMap φ h_over hIJ).left ∧
              cU.ι.app I ≫ iU.inv ≫ f ≫ iV.hom =
                (𝒮.bigTopology S).sheafifiedRepresentableMap
                    ((𝒮.bigAffineInclusion S).map t) ≫ cV.ι.app J :=
  sorry

end correspondsTo

end AlgebraicGeometry.IsLocallyCountablyIndexed
