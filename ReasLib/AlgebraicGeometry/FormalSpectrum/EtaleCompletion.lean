module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Comma.Over.Basic
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

open CategoryTheory AlgebraicGeometry Opposite TopologicalRing
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
  sorry

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
      spfMap_weakIdealCompletion hB A' :=
  sorry

/-- Formal spectrum of a continuous algebra homomorphism commutes with the maps
to the formal spectrum of the base ring. -/
theorem spfEtaleCompletionHom_over {A A' : CommAlgCat.EtaleCompletion B}
    (f : A ⟶ A') :
    (let φ := CommAlgCat.EtaleCompletion.homEquiv A A' f;
      spfMap (hA := specHom_weakIdealCompletion hB A.obj)
        (hB := specHom_weakIdealCompletion hB A'.obj) φ.val φ.property.1 (by
          dsimp only [specHom_weakIdealCompletion]
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.property.2])).hom ≫ (spfMap_weakIdealCompletion hB A.obj).hom =
      (spfMap_weakIdealCompletion hB A'.obj).hom :=
  sorry

/-- Formal spectrum sends the identity of a completed algebra to the identity. -/
theorem spfEtaleCompletionHom_id (A : CommAlgCat.EtaleCompletion B) :
    (let φ := CommAlgCat.EtaleCompletion.homEquiv A A (𝟙 A);
      spfMap (hA := specHom_weakIdealCompletion hB A.obj)
        (hB := specHom_weakIdealCompletion hB A.obj) φ.val φ.property.1 (by
          dsimp only [specHom_weakIdealCompletion]
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.property.2])) =
      𝟙 (spf (weakIdealCompletion B A.obj) (specHom_weakIdealCompletion hB A.obj)) :=
  sorry

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
  sorry

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
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace

namespace AlgebraicGeometry.FormalAlgebraicSpace

open AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The functor of points of a weakly admissible formal spectrum is a formal
algebraic space. -/
instance instIsFormalAlgebraicSpace_spf {S : Scheme.{u}} {B : Type u}
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsWeaklyAdmissibleRing B]
    (hB : Spec (.of B) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    IsFormalAlgebraicSpace (spf B hB).obj :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace

