module

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Coproduct
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Finite constant sheaves on the small étale slice

For an affine object `U`, a finite set is represented by the spectrum of the
finite product of the global section ring. The inverse sheaf map glues the labels
on the disjoint component cover, allowing different labels on disconnected tests.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Etale.ConstantFiniteRepresentation

variable {X : Scheme.{u}} (U : X.Etale) [IsAffine U.left]
variable (E : Type (u + 1)) [Finite E]

/-- The trivial finite cover is the spectrum of one copy of the affine ring per label. -/
def structureMap : Spec (.of (Fin (Nat.card E) → Γ(U.left, ⊤))) ⟶ U.left :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤)
    (Fin (Nat.card E) → Γ(U.left, ⊤)))) ≫ U.left.isoSpec.inv

instance structureMap_etale : Etale (structureMap U E) := sorry

instance structureMap_finite : IsFinite (structureMap U E) := sorry

/-- The finite product spectrum as an object of the small étale slice at `U`. -/
def object : Over U :=
  Over.mk (MorphismProperty.Over.homMk (structureMap U E) (by rfl) :
    Scheme.Etale.mk (structureMap U E ≫ U.hom) ⟶ U)

variable {E} (labels : E ≃ Fin (Nat.card E))

/-- The branch labelled by `e` is induced by evaluation at its finite index. -/
def component (e : E) : U.left ⟶ (object U E).left.left :=
  U.left.isoSpec.hom ≫ Spec.map
    (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin (Nat.card E) ↦ Γ(U.left, ⊤))
      (labels e)))

/-- Each branch is a section of the structure map. -/
theorem component_structureMap (e : E) : component U labels e ≫ structureMap U E = 𝟙 U.left :=
  sorry

/-- The branch inclusion is a morphism from the terminal object of the slice. -/
def inclusion (e : E) : Over.mk (𝟙 U) ⟶ object U E :=
  Over.homMk (MorphismProperty.Over.homMk (component U labels e) (by
    change component U labels e ≫ (structureMap U E ≫ U.hom) = U.hom
    rw [← Category.assoc, component_structureMap, Category.id_comp])) (by
    apply MorphismProperty.Over.Hom.ext
    exact component_structureMap U labels e)

instance inclusion_mono (e : E) : Mono (inclusion U labels e) := sorry

/-- The covering cofan of the finite product spectrum has one affine branch per label. -/
def cofan : Cofan fun _ : E ↦ Over.mk (𝟙 U) :=
  Cofan.mk (object U E) (inclusion U labels)

/-- The finite product spectrum is covered by its evaluation branches. -/
theorem covering : Sieve.ofArrows _ (cofan U labels).inj ∈
    (X.smallEtaleTopology.over U) (object U E) := sorry

/-- Two distinct labels have empty intersection in the étale slice. -/
theorem disjoint {i j : E} (hij : i ≠ j) {V : Over U}
    (a : V ⟶ Over.mk (𝟙 U)) (b : V ⟶ Over.mk (𝟙 U))
    (hab : a ≫ (cofan U labels).inj i = b ≫ (cofan U labels).inj j) :
    (⊥ : Sieve V) ∈ (X.smallEtaleTopology.over U) V := sorry

/-- The finite constant sheaf is represented by the actual finite product spectrum.
The inverse is the amalgamation of local component labels, including on disconnected tests. -/
def iso [HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))] :
    (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E ≅
      (X.smallEtaleTopology.over U).sheafifiedRepresentable (object U E) := by
  letI : ∀ i, Mono ((cofan U labels).inj i) := fun i ↦
    inferInstanceAs (Mono (inclusion U labels i))
  exact GrothendieckTopology.constantSheafIsoOfDisjointCover.{u + 1, u + 1, u}
    (X.smallEtaleTopology.over U) Over.mkIdTerminal E (cofan U labels)
    (covering U labels) (disjoint U labels)

/-- Pulling the inverse comparison back to a branch returns precisely its label. -/
theorem iso_inv_inclusion
    [HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))] (e : E) :
    (X.smallEtaleTopology.over U).sheafifiedRepresentableMap (inclusion U labels e) ≫
      (iso U labels).inv =
        (GrothendieckTopology.constantSheafCofan.{u + 1, u + 1, u}
          (X.smallEtaleTopology.over U)
          (T := Over.mk (𝟙 U)) E).inj e := sorry

/-- A constant label maps to the associated evaluation branch of the product spectrum. -/
theorem iso_hom_inclusion
    [HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))] (e : E) :
    (GrothendieckTopology.constantSheafCofan.{u + 1, u + 1, u}
          (X.smallEtaleTopology.over U)
        (T := Over.mk (𝟙 U)) E).inj e ≫ (iso U labels).hom =
      (X.smallEtaleTopology.over U).sheafifiedRepresentableMap (inclusion U labels e) := sorry

end AlgebraicGeometry.Scheme.Etale.ConstantFiniteRepresentation
