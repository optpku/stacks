/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Modules

/-- The module-sheaf pseudofunctor on schemes, retaining its pullback functors. -/
noncomputable abbrev descentPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  pseudofunctor.comp Bicategory.Adj.forget₁

/-- The fibre of `descentPseudofunctor` over a scheme is its category of module sheaves. -/
theorem descentPseudofunctor_obj (X : Scheme.{u}) :
    descentPseudofunctor.obj (.mk (.op X)) = Cat.of X.Modules := sorry

/-- The action of `descentPseudofunctor` on a scheme morphism is module pullback. -/
theorem descentPseudofunctor_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (descentPseudofunctor.map f.op.toLoc).toFunctor = pullback f := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.QCoh

open ObjectProperty

variable {I : Type v} {S : Scheme.{u}} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)

/-- The property that every component of canonical module descent data is quasi-coherent. -/
abbrev descentProperty :
    ObjectProperty (Modules.descentPseudofunctor.DescentData f) :=
  fun D ↦ ∀ i, (D.obj i).IsQuasicoherent

/-- Componentwise characterization of the quasi-coherence property on canonical descent data. -/
theorem descentProperty_iff (D : Modules.descentPseudofunctor.DescentData f) :
    descentProperty X f D ↔ ∀ i, (D.obj i).IsQuasicoherent := sorry

/-- Componentwise quasi-coherence is invariant under isomorphisms of descent data. -/
instance descentPropertyIsClosedUnderIsomorphisms :
    (descentProperty X f).IsClosedUnderIsomorphisms := sorry

/-- Quasi-coherent descent data for the family `f : ∀ i, X i ⟶ S`. -/
abbrev DescentData :=
  (descentProperty X f).FullSubcategory

namespace DescentData

/-- Regard canonical module descent data with quasi-coherent components as quasi-coherent
descent data. -/
def of (D : Modules.descentPseudofunctor.DescentData f)
    (hD : ∀ i, (D.obj i).IsQuasicoherent) : DescentData X f :=
  ⟨D, hD⟩

/-- The underlying canonical descent datum of `of` is the supplied datum. -/
theorem of_obj (D : Modules.descentPseudofunctor.DescentData f)
    (hD : ∀ i, (D.obj i).IsQuasicoherent) :
    (of X f D hD).obj = D := sorry

/-- Every component of quasi-coherent descent data is quasi-coherent. -/
theorem localIsQuasicoherent (D : DescentData X f) (i : I) :
    (D.obj.obj i).IsQuasicoherent := sorry

/-- Two morphisms of quasi-coherent descent data are equal when all component maps agree. -/
theorem homExt {D E : DescentData X f} {a b : D ⟶ E}
    (h : ∀ i, a.hom.hom i = b.hom.hom i) : a = b := sorry

/-- The property that every component in a chosen-overlap presentation is quasi-coherent. -/
abbrev chosenProperty
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)) :
    ObjectProperty (Modules.descentPseudofunctor.DescentData' sq sq₃) :=
  fun D ↦ ∀ i, (D.obj i).IsQuasicoherent

/-- Componentwise characterization of quasi-coherence in a chosen-overlap presentation. -/
theorem chosenProperty_iff
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (D : Modules.descentPseudofunctor.DescentData' sq sq₃) :
    chosenProperty X f sq sq₃ D ↔ ∀ i, (D.obj i).IsQuasicoherent := sorry

/-- The chosen pairwise- and triple-overlap presentation of quasi-coherent descent data. -/
abbrev Chosen
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)) :=
  (chosenProperty X f sq sq₃).FullSubcategory

namespace Chosen

variable (sq : ∀ i j, ChosenPullback (f i) (f j))
variable (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))

/-- Regard chosen-overlap descent data with quasi-coherent components as a chosen
quasi-coherent descent datum. -/
def of (D : Modules.descentPseudofunctor.DescentData' sq sq₃)
    (hD : ∀ i, (D.obj i).IsQuasicoherent) : Chosen X f sq sq₃ :=
  ⟨D, hD⟩

/-- The underlying chosen-overlap descent datum of `of` is the supplied datum. -/
theorem of_obj (D : Modules.descentPseudofunctor.DescentData' sq sq₃)
    (hD : ∀ i, (D.obj i).IsQuasicoherent) :
    (of X f sq sq₃ D hD).obj = D := sorry

/-- The source comparison morphism on a chosen pairwise overlap, as an isomorphism. -/
noncomputable def transitionIso (D : Chosen X f sq sq₃) (i j : I) :=
  asIso (D.obj.hom i j)

/-- The forward map of `transitionIso` is the chosen descent comparison morphism. -/
theorem transitionIso_hom (D : Chosen X f sq sq₃) (i j : I) :
    (transitionIso X f sq sq₃ D i j).hom = D.obj.hom i j := sorry

/-- The comparison isomorphisms satisfy the cocycle condition on each chosen triple overlap. -/
theorem cocycle (D : Chosen X f sq sq₃) (i j k : I) :
    Pseudofunctor.DescentData'.pullHom' D.obj.hom (sq₃ i j k).p
        (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
      Pseudofunctor.DescentData'.pullHom' D.obj.hom (sq₃ i j k).p
        (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom' D.obj.hom (sq₃ i j k).p
        (sq₃ i j k).p₁ (sq₃ i j k).p₃ := sorry

/-- A morphism of chosen descent data commutes with each pairwise comparison morphism. -/
theorem hom_compatibility {D E : Chosen X f sq sq₃} (g : D ⟶ E) (i j : I) :
    (Modules.descentPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.map (g.hom.hom i) ≫
        E.obj.hom i j =
      D.obj.hom i j ≫
        (Modules.descentPseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.map
          (g.hom.hom j) := sorry

/-- The canonical descent equivalence carries the chosen quasi-coherence property to the
canonical quasi-coherence property. -/
theorem inverseImage_descentProperty :
    (descentProperty X f).inverseImage
        (Pseudofunctor.DescentData'.descentDataEquivalence
          Modules.descentPseudofunctor sq sq₃).functor =
      chosenProperty X f sq sq₃ := sorry

/-- The canonical equivalence between chosen-overlap and representation-independent
quasi-coherent descent data. -/
noncomputable def equivalence : Chosen X f sq sq₃ ≌ DescentData X f :=
  (Pseudofunctor.DescentData'.descentDataEquivalence
      Modules.descentPseudofunctor sq sq₃).congrFullSubcategory
    (inverseImage_descentProperty X f sq sq₃)

/-- The chosen-to-canonical equivalence retains every component object. -/
theorem equivalence_functor_obj_obj (D : Chosen X f sq sq₃) (i : I) :
    ((equivalence X f sq sq₃).functor.obj D).obj.obj i = D.obj.obj i := sorry

/-- The chosen-to-canonical equivalence retains every component of a morphism. -/
theorem equivalence_functor_map_hom {D E : Chosen X f sq sq₃}
    (g : D ⟶ E) (i : I) :
    ((equivalence X f sq sq₃).functor.map g).hom.hom i = g.hom.hom i := sorry

end Chosen

end DescentData

end AlgebraicGeometry.Scheme.QCoh
