module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap69.Lemma_69_11_2_Flat_base_change_BaseChange

/-!
# Formal glueing of quasi-coherent modules

The category `QCoh(Y → X, Z)` of triples `(H, G, φ)` is the categorical pullback of
quasi-coherent pullback along `f|_V : V ⟶ U` and along `j' : V ⟶ Y`. The canonical
functor `QCoh X ⥤ QCoh(Y → X, Z)` sends `F` to `(F|_U, f^* F, can)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

/-- Successive quasi-coherent pullbacks identify with pullback along the composite,
by lifting `Modules.pullbackCompIso`. -/
def pullbackCompIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  NatIso.ofComponents
    (fun F ↦
      (quasiCoherentModuleProperty X).isoMk ((Modules.pullbackCompIso f g).symm.app F.obj))
    sorry

/-- The restriction `f|_V : V ⟶ U` of `f : Y ⟶ X` to the open complements of `Z` and
`f⁻¹Z`. -/
def restrict {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    closedImmersionComplement (inverseImageι f i) ⟶ closedImmersionComplement i where
  app W := TypeCat.ofHom fun t ↦
    ⟨(closedImmersionComplementι (inverseImageι f i) ≫ f).app W t, sorry⟩
  naturality := sorry

/-- The square with vertices `V`, `Y`, `U`, `X` commutes: `restrict ≫ j = j' ≫ f`. -/
theorem restrict_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    restrict f i ≫ closedImmersionComplementι i =
      closedImmersionComplementι (inverseImageι f i) ≫ f :=
  sorry

/-- The category `QCoh(Y → X, Z)` of triples `(H, G, φ)` with `H` quasi-coherent on
`U = X \ Z`, `G` quasi-coherent on `Y`, and `φ : (f|_V)^* H ≅ G|_V`. -/
abbrev category {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :=
  CategoricalPullback (pullback (restrict f i))
    (pullback (closedImmersionComplementι (inverseImageι f i)))

/-- The canonical isomorphism `(f|_V)^* (F|_U) ≅ (f^* F)|_V`. -/
def can {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    pullback (closedImmersionComplementι i) ⋙ pullback (restrict f i) ≅
      pullback f ⋙ pullback (closedImmersionComplementι (inverseImageι f i)) :=
  (pullbackCompIso (restrict f i) (closedImmersionComplementι i)).symm ≪≫
    pullbackCompIso (closedImmersionComplementι (inverseImageι f i)) f

/-- The canonical functor `QCoh X ⥤ QCoh(Y → X, Z)` sending `F` to
`(F|_U, f^* F, can)`. -/
def functor {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    QCoh X ⥤ category f i :=
  (CatCommSqOver.toFunctorToCategoricalPullback
      (pullback (restrict f i))
      (pullback (closedImmersionComplementι (inverseImageι f i)))
      (QCoh X)).obj
    { fst := pullback (closedImmersionComplementι i)
      snd := pullback f
      iso := can f i }

/-- An object of `QCoh(Y → X, Z)` from a triple `(H, G, φ)`. -/
def mk {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] {H : QCoh (closedImmersionComplement i)} {G : QCoh Y}
    (φ : (pullback (restrict f i)).obj H ≅
      (pullback (closedImmersionComplementι (inverseImageι f i))).obj G) :
    category f i :=
  ⟨H, G, φ⟩

/-- The first component of the canonical glueing functor is restriction along `j : U ⟶ X`. -/
theorem obj_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (F : QCoh X) :
    ((functor f i).obj F).fst = (pullback (closedImmersionComplementι i)).obj F :=
  sorry

/-- The second component of the canonical glueing functor is pullback along `f`. -/
theorem obj_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (F : QCoh X) :
    ((functor f i).obj F).snd = (pullback f).obj F :=
  sorry

/-- The structural isomorphism of the canonical glueing functor is the component of `can`. -/
theorem obj_iso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (F : QCoh X) :
    ((functor f i).obj F).iso = (can f i).app F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing
