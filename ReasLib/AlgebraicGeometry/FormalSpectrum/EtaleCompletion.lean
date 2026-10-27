/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.Topology.Category.TopCommRingCat
public import ReasLib.RingTheory.Etale.Category
public import ReasLib.RingTheory.Topology.WeakIdealCompletion.Map
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineEtaleOver
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Morphism

/-!
# Étale completions and formal spectra

The category of completed étale algebras has continuous algebra homomorphisms
as morphisms. Formal spectrum acts contravariantly on these maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalRing
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace CommAlgCat

variable (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- Weak-ideal completions of étale algebras, with all continuous algebra homomorphisms.
Objects retain an étale presentation; morphisms depend only on their completed algebras. -/
abbrev EtaleCompletion :=
  InducedCategory (Under (TopCommRingCat.of B))
    (fun A : Etale.{u} B =>
      Under.mk (X := TopCommRingCat.of B)
        (Y := TopCommRingCat.of (weakIdealCompletion B A))
        ⟨algebraMap B (weakIdealCompletion B A), TopologicalRing.continuous_algebraMap B A⟩)

/-- An étale algebra determines its actual weak-ideal completion as a categorical object. -/
def EtaleCompletion.of (A : Type u) [CommRing A] [Algebra B A]
    [Algebra.Etale B A] : EtaleCompletion B :=
  Etale.of B A

variable {B}

/-- Morphisms between completed étale algebras are precisely continuous ring
homomorphisms commuting with the structural maps from the base ring. -/
def EtaleCompletion.homEquiv (A A' : EtaleCompletion B) :
    (A ⟶ A') ≃
      {φ : weakIdealCompletion B A.obj →+* weakIdealCompletion B A'.obj //
        Continuous φ ∧
          φ.comp (algebraMap B (weakIdealCompletion B A.obj)) =
            algebraMap B (weakIdealCompletion B A'.obj)} where
  toFun f := ⟨f.hom.right.val, f.hom.right.property,
    congrArg Subtype.val (Under.w f.hom)⟩
  invFun φ := InducedCategory.homMk
    (Under.homMk ⟨φ.val, φ.property.1⟩ (Subtype.ext φ.property.2))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end CommAlgCat

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

open TopologicalRing

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]

/-- The structure morphism `Spec((A)^∧) ⟶ S` of the weak-ideal completion of a
`B`-algebra, obtained by composing `Spec` of `B → (A)^∧` with the structure
morphism of `B`. -/
def specHom_weakIdealCompletion (hB : Spec (.of B) ⟶ S) (A : Type u)
    [CommRing A] [Algebra B A] :
    Spec (.of (weakIdealCompletion B A)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap B (weakIdealCompletion B A))) ≫ hB

/-- `specHom_weakIdealCompletion` is `Spec` of the algebra map `B → (A)^∧`
followed by the structure morphism of `B`. -/
theorem specHom_weakIdealCompletion_comp (hB : Spec (.of B) ⟶ S) (A : Type u)
    [CommRing A] [Algebra B A] :
    specHom_weakIdealCompletion hB A =
      Spec.map (CommRingCat.ofHom (algebraMap B (weakIdealCompletion B A))) ≫ hB :=
  rfl

/-- Algebra homomorphisms induce maps of completed spectra over the base scheme. -/
theorem specHom_weakIdealCompletion_map [TopologicalRing.IsWeaklyAdmissibleRing B]
    (hB : Spec (.of B) ⟶ S) {A A' : Type u} [CommRing A] [Algebra B A]
    [CommRing A'] [Algebra B A'] (f : A →ₐ[B] A') :
    Spec.map (CommRingCat.ofHom (weakIdealCompletion.map f)) ≫
        specHom_weakIdealCompletion hB A = specHom_weakIdealCompletion hB A' :=
  by
    have h : (weakIdealCompletion.map f).comp
        (algebraMap B (weakIdealCompletion B A)) =
          algebraMap B (weakIdealCompletion B A') := by
      ext b
      apply Subtype.ext
      funext I
      change Ideal.Quotient.mk _ (f (algebraMap B A b)) =
        Ideal.Quotient.mk _ (algebraMap B A' b)
      rw [f.commutes]
    dsimp only [specHom_weakIdealCompletion]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- Formal spectrum sends the identity ring map to the identity. -/
theorem spfMap_id {S : Scheme.{u}} (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    spfMap (RingHom.id A) continuous_id (by simp) = 𝟙 (spf A hA) := by
  apply colimit.hom_ext
  intro I
  change spfι A hA I ≫ spfMap _ _ _ = spfι A hA I ≫ 𝟙 _
  rw [← spfMap_comm (RingHom.id A) continuous_id (by simp)
    (I := I) (J := I) le_rfl]
  have hi : stageMap (RingHom.id A) (by simp) (I := I) (J := I) le_rfl =
      𝟙 (stage A hA I) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom _) = 𝟙 _
    have hq : Ideal.Quotient.lift I.ideal
        ((Ideal.Quotient.mk I.ideal).comp (RingHom.id A))
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr ha) =
          RingHom.id (A ⧸ I.ideal) := by
      ext a
      rfl
    rw [hq]
    exact Spec.map_id _
  simp only [hi, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- Formal spectrum reverses composition of continuous ring maps over the base. -/
theorem spfMap_comp {S : Scheme.{u}} {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B]
    [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C]
    {hA : Spec (.of A) ⟶ S} {hB : Spec (.of B) ⟶ S} {hC : Spec (.of C) ⟶ S}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (φ : A →+* B) (ψ : B →+* C) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφS : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    (hψS : Spec.map (CommRingCat.ofHom ψ) ≫ hB = hC) :
    spfMap ψ hψ hψS ≫ spfMap φ hφ hφS =
      spfMap (ψ.comp φ) (hψ.comp hφ) (by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφS, hψS]) := by
  let hcomp : Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ hA = hC := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφS, hψS]
  apply colimit.hom_ext
  intro K
  obtain ⟨J₀, hJ₀⟩ :=
    IsWeaklyPreadmissibleRing.exists_ideal_isWeakIdealOfDefinition (R := B)
  obtain ⟨I₀, hI₀⟩ :=
    IsWeaklyPreadmissibleRing.exists_ideal_isWeakIdealOfDefinition (R := A)
  let J := WeakIdealOfDefinition.of (J₀ ⊓ Ideal.comap ψ K.ideal)
    (TopologicalRing.Ideal.IsWeakIdealOfDefinition.inf_of_isOpen hJ₀
      (K.isWeak.1.preimage hψ))
  let I := WeakIdealOfDefinition.of (I₀ ⊓ Ideal.comap φ J.ideal)
    (TopologicalRing.Ideal.IsWeakIdealOfDefinition.inf_of_isOpen hI₀
      (J.isWeak.1.preimage hφ))
  have hJK : J.ideal ≤ Ideal.comap ψ K.ideal := inf_le_right
  have hIJ : I.ideal ≤ Ideal.comap φ J.ideal := inf_le_right
  have hIK : I.ideal ≤ Ideal.comap (ψ.comp φ) K.ideal := fun _ h => hJK (hIJ h)
  have hstage : stageMap (ψ.comp φ) hcomp hIK =
      stageMap ψ hψS hJK ≫ stageMap φ hφS hIJ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom _) =
      Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    rfl
  change spfι C hC K ≫ (spfMap ψ hψ hψS ≫ spfMap φ hφ hφS) =
    spfι C hC K ≫ spfMap (ψ.comp φ) (hψ.comp hφ) hcomp
  calc
    _ = ((presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (stageMap ψ hψS hJK)) ≫ spfι B hB J) ≫
            spfMap φ hφ hφS := by
      rw [← Category.assoc, ← spfMap_comm ψ hψ hψS hJK]
    _ = (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (stageMap ψ hψS hJK)) ≫
        ((presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (stageMap φ hφS hIJ)) ≫ spfι A hA I) := by
      rw [Category.assoc, ← spfMap_comm φ hφ hφS hIJ]
    _ = (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (stageMap ψ hψS hJK ≫ stageMap φ hφS hIJ)) ≫
            spfι A hA I := by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [← hstage, spfMap_comm (ψ.comp φ) (hψ.comp hφ) hcomp hIK]

end AlgebraicGeometry.AffineFormalAlgebraicSpace

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/-- `Spf` of a weakly admissible ring over `S` is a directed affine thickening
colimit. -/
theorem exists_isDirectedAffineThickeningColimit_spf (A : Type u) [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D (spf A hA).obj :=
  sorry

/-- The morphism `Spf((A)^∧) ⟶ Spf(B)` induced by the algebra map
`B → (A)^∧`. -/
def spfMap_weakIdealCompletion (A : Type u) [CommRing A] [Algebra B A] :
    spf (weakIdealCompletion B A) (specHom_weakIdealCompletion hB A) ⟶
      spf B hB :=
  spfMap (algebraMap B (weakIdealCompletion B A)) (continuous_algebraMap B A) rfl

/-- The underlying functor-of-points morphism of `spfMap_weakIdealCompletion`. -/
theorem spfMap_weakIdealCompletion_hom (A : Type u) [CommRing A] [Algebra B A] :
    (spfMap_weakIdealCompletion hB A).hom =
      (spfMap (algebraMap B (weakIdealCompletion B A))
        (continuous_algebraMap B A) rfl).hom :=
  rfl

/-- `Spf((A)^∧) ⟶ Spf(B)` is representable by algebraic spaces and étale when
`A` is an étale `B`-algebra. -/
instance instEtale_spfMap_weakIdealCompletion (A : Type u) [CommRing A]
    [Algebra B A] [Algebra.Etale B A] :
    FormalAlgebraicSpace.Etale (spfMap_weakIdealCompletion hB A).hom :=
  sorry

/-- The morphism `Spf((A')^∧) ⟶ Spf((A)^∧)` induced by a `B`-algebra map
`A →ₐ[B] A'`. -/
def spfMap_weakIdealCompletion_map {A A' : Type u} [CommRing A] [Algebra B A]
    [CommRing A'] [Algebra B A'] (f : A →ₐ[B] A') :
    spf (weakIdealCompletion B A') (specHom_weakIdealCompletion hB A') ⟶
      spf (weakIdealCompletion B A) (specHom_weakIdealCompletion hB A) :=
  spfMap (weakIdealCompletion.map f) (weakIdealCompletion.continuous_map f)
    (specHom_weakIdealCompletion_map hB f)

/-- `spfMap_weakIdealCompletion_map f` lies over `Spf(B)`. -/
theorem spfMap_weakIdealCompletion_map_comp {A A' : Type u} [CommRing A]
    [Algebra B A] [CommRing A'] [Algebra B A'] (f : A →ₐ[B] A') :
    spfMap_weakIdealCompletion_map hB f ≫ spfMap_weakIdealCompletion hB A =
      spfMap_weakIdealCompletion hB A' := by
  refine (spfMap_comp (hA := hB)
    (hB := specHom_weakIdealCompletion hB A)
    (hC := specHom_weakIdealCompletion hB A')
    (algebraMap B (weakIdealCompletion B A)) (weakIdealCompletion.map f)
    (continuous_algebraMap B A) (weakIdealCompletion.continuous_map f)
    rfl (specHom_weakIdealCompletion_map hB f)).trans ?_
  congr 1
  ext b
  apply Subtype.ext
  funext I
  change Ideal.Quotient.mk _ (f (algebraMap B A b)) =
    Ideal.Quotient.mk _ (algebraMap B A' b)
  rw [f.commutes]

/-- Formal spectrum of a continuous algebra homomorphism commutes with the maps
to the formal spectrum of the base ring. -/
theorem spfEtaleCompletionHom_over {A A' : CommAlgCat.EtaleCompletion B}
    (f : A ⟶ A') :
    (let φ := CommAlgCat.EtaleCompletion.homEquiv A A' f;
      spfMap (hA := specHom_weakIdealCompletion hB A.obj)
        (hB := specHom_weakIdealCompletion hB A'.obj) φ.val φ.property.1 (by
          dsimp only [specHom_weakIdealCompletion]
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.property.2])).hom ≫ (spfMap_weakIdealCompletion hB A.obj).hom =
      (spfMap_weakIdealCompletion hB A'.obj).hom := by
  let φ := CommAlgCat.EtaleCompletion.homEquiv A A' f
  change (spfMap φ.val φ.property.1 _ ≫
    spfMap (algebraMap B (weakIdealCompletion B A.obj))
      (continuous_algebraMap B A.obj) rfl).hom = _
  rw [spfMap_comp]
  congr 2
  exact φ.property.2

/-- Formal spectrum sends the identity of a completed algebra to the identity. -/
theorem spfEtaleCompletionHom_id (A : CommAlgCat.EtaleCompletion B) :
    (let φ := CommAlgCat.EtaleCompletion.homEquiv A A (𝟙 A);
      spfMap (hA := specHom_weakIdealCompletion hB A.obj)
        (hB := specHom_weakIdealCompletion hB A.obj) φ.val φ.property.1 (by
          dsimp only [specHom_weakIdealCompletion]
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.property.2])) =
      𝟙 (spf (weakIdealCompletion B A.obj) (specHom_weakIdealCompletion hB A.obj)) := by
  exact spfMap_id _ _

/-- Formal spectrum reverses composition of continuous completed-algebra maps. -/
theorem spfEtaleCompletionHom_comp {A A' A'' : CommAlgCat.EtaleCompletion B}
    (f : A ⟶ A') (g : A' ⟶ A'') :
    (let φ := CommAlgCat.EtaleCompletion.homEquiv A A'' (f ≫ g);
      spfMap (hA := specHom_weakIdealCompletion hB A.obj)
        (hB := specHom_weakIdealCompletion hB A''.obj) φ.val φ.property.1 (by
          dsimp only [specHom_weakIdealCompletion]
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.property.2])) =
      (let φ := CommAlgCat.EtaleCompletion.homEquiv A' A'' g;
      spfMap (hA := specHom_weakIdealCompletion hB A'.obj)
        (hB := specHom_weakIdealCompletion hB A''.obj) φ.val φ.property.1 (by
          dsimp only [specHom_weakIdealCompletion]
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.property.2])) ≫
        (let φ := CommAlgCat.EtaleCompletion.homEquiv A A' f;
      spfMap (hA := specHom_weakIdealCompletion hB A.obj)
        (hB := specHom_weakIdealCompletion hB A'.obj) φ.val φ.property.1 (by
          dsimp only [specHom_weakIdealCompletion]
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.property.2])) :=
  by
    let φ := CommAlgCat.EtaleCompletion.homEquiv A A' f
    let ψ := CommAlgCat.EtaleCompletion.homEquiv A' A'' g
    have hφS : Spec.map (CommRingCat.ofHom φ.val) ≫
        specHom_weakIdealCompletion hB A.obj =
          specHom_weakIdealCompletion hB A'.obj := by
      dsimp only [specHom_weakIdealCompletion]
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.property.2]
    have hψS : Spec.map (CommRingCat.ofHom ψ.val) ≫
        specHom_weakIdealCompletion hB A'.obj =
          specHom_weakIdealCompletion hB A''.obj := by
      dsimp only [specHom_weakIdealCompletion]
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ψ.property.2]
    exact (spfMap_comp φ.val ψ.val φ.property.1 ψ.property.1 hφS hψS).symm

/-- Formal spectrum sends completed étale algebras contravariantly to affine
formal algebraic spaces representably étale over the base formal spectrum. -/
def spfEtaleCompletion :
    (CommAlgCat.EtaleCompletion.{u} B)ᵒᵖ ⥤ AffineEtaleOver (spf B hB).obj where
  obj A :=
    AffineEtaleOver.mk (spfMap_weakIdealCompletion hB A.unop.obj).hom
      (exists_isDirectedAffineThickeningColimit_spf
        (weakIdealCompletion B A.unop.obj) (specHom_weakIdealCompletion hB A.unop.obj))
  map {A A'} f :=
    InducedCategory.homMk
      (MorphismProperty.Over.homMk (let φ := CommAlgCat.EtaleCompletion.homEquiv A'.unop A.unop f.unop;
      spfMap (hA := specHom_weakIdealCompletion hB A'.unop.obj)
        (hB := specHom_weakIdealCompletion hB A.unop.obj) φ.val φ.property.1 (by
          dsimp only [specHom_weakIdealCompletion]
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.property.2])).hom
        (spfEtaleCompletionHom_over hB f.unop))
  map_id A := by
    apply InducedCategory.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f => f.hom) (spfEtaleCompletionHom_id hB A.unop)
  map_comp f g := by
    apply InducedCategory.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f => f.hom) (spfEtaleCompletionHom_comp hB g.unop f.unop)

/-- The object of the formal-spectrum functor is the formal spectrum of the
actual weak-ideal completion with its canonical structural morphism. -/
theorem spfEtaleCompletion_obj (A : CommAlgCat.EtaleCompletion.{u} B) :
    ((spfEtaleCompletion hB).obj (op A)).obj.hom =
      (spfMap_weakIdealCompletion hB A.obj).hom :=
  rfl

/-- The formal-spectrum functor acts on every completed-algebra morphism by
the formal-spectrum map of its continuous ring homomorphism. -/
theorem spfEtaleCompletion_map {A A' : CommAlgCat.EtaleCompletion.{u} B}
    (f : A ⟶ A') :
    ((spfEtaleCompletion hB).map f.op).hom.left =
      (let φ := CommAlgCat.EtaleCompletion.homEquiv A A' f;
      spfMap (hA := specHom_weakIdealCompletion hB A.obj)
        (hB := specHom_weakIdealCompletion hB A'.obj) φ.val φ.property.1 (by
          dsimp only [specHom_weakIdealCompletion]
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.property.2])).hom :=
  rfl

/-- Formal spectrum is an equivalence from the opposite category of completed
étale algebras to representably étale affine formal algebraic spaces over the base. -/
instance instIsEquivalence_spfEtaleCompletion :
    (spfEtaleCompletion hB).IsEquivalence :=
  sorry

/-- An affine formal algebraic space representably étale over a weakly admissible
formal spectrum is itself the formal spectrum of a weakly admissible ring. -/
theorem isMcQuillanAffine_of_affineEtaleOver (X : AffineEtaleOver (spf B hB).obj) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing A) (hA : Spec (.of A) ⟶ S),
      Nonempty (X.obj.left ≅ (spf A hA).obj) :=
  by
    obtain ⟨A, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (spfEtaleCompletion hB) X
    refine ⟨weakIdealCompletion B A.unop.obj, inferInstance, inferInstance, inferInstance,
      specHom_weakIdealCompletion hB A.unop.obj, ⟨?_⟩⟩
    exact
      { hom := e.inv.hom.left
        inv := e.hom.hom.left
        hom_inv_id := congrArg (fun f => f.hom.left) e.inv_hom_id
        inv_hom_id := congrArg (fun f => f.hom.left) e.hom_inv_id }

end AlgebraicGeometry.AffineFormalAlgebraicSpace

namespace AlgebraicGeometry.FormalAlgebraicSpace

open AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The functor of points of a weakly admissible formal spectrum is a formal
algebraic space. -/
instance instIsFormalAlgebraicSpace_spf {S : Scheme.{u}} {B : Type u}
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsWeaklyAdmissibleRing B]
    (hB : Spec (.of B) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    IsFormalAlgebraicSpace (spf B hB).obj := by
  refine ⟨(spf B hB).property, ?_, ?_⟩
  · refine ⟨PUnit, fun _ => (spf B hB).obj, fun _ => 𝟙 _, ?_, ?_, ?_, ?_⟩
    · intro _
      exact exists_isDirectedAffineThickeningColimit_spf B hB
    · intro _
      exact FormalAlgebraicSpace.Etale.representable (f := 𝟙 (spf B hB).obj)
    · intro _ ha U ξ
      exact FormalAlgebraicSpace.Etale.of_pullback (f := 𝟙 (spf B hB).obj) ξ
    · apply Presheaf.isLocallySurjective_of_surjective
      intro T x
      exact ⟨⟨PUnit.unit, x⟩, rfl⟩
  · obtain ⟨U, R, π, σ, hπ, hσ⟩ := spf_existsPresentation B hB
    let J := Scheme.fppfTopology.over S
    let F := sheafToPresheaf J (Type u)
    let eU : yoneda.obj U ≅ ((presheafToSheaf J (Type u)).obj (yoneda.obj U)).obj :=
      isoSheafify J ((isSheaf_iff_isSheaf_of_type J _).2
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))
    let eR : yoneda.obj R ≅ ((presheafToSheaf J (Type u)).obj (yoneda.obj R)).obj :=
      isoSheafify J ((isSheaf_iff_isSheaf_of_type J _).2
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))
    let πU := eU.hom ≫ π.hom
    let q := pullback.map π.hom π.hom πU πU eU.inv eU.inv (𝟙 _)
      (by simp [πU]) (by simp [πU])
    let eP : (pullback π π).obj ≅ pullback π.hom π.hom :=
      PreservesPullback.iso F π π
    let σR := eR.hom ≫ σ.hom ≫ eP.hom ≫ q
    refine ⟨U, R, πU, σR, ?_, ?_⟩
    · dsimp only [πU]
      infer_instance
    · haveI : IsIso q := by
        dsimp only [q]
        infer_instance
      haveI : Presheaf.IsLocallySurjective J σ.hom := hσ
      dsimp only [σR]
      infer_instance

end AlgebraicGeometry.FormalAlgebraicSpace

