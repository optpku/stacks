module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import ReasLib.CategoryTheory.Monoidal.Bimod.Module
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative internal Hom for bimodule objects

Let `N` be an `(A, B)`-bimodule in a monoidal category with a chosen right internal Hom.  This file constructs
`Hom_B(N, -)` as the equalizer imposing compatibility with the right `B`-actions.  It is the
right adjoint of balanced tensoring with `N`.  The construction is independent of rings,
gradings, complexes, and sheaves.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

noncomputable section

universe u v

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [HasEqualizers C] [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {A B : Mon C}

/-- Balanced tensoring with an `(A, B)`-bimodule, restricted to right-module categories. -/
@[stacks 0FR6 "relative tensor functor on right modules"]
noncomputable abbrev tensorWith (N : Bimod A B) : RightModule A ⥤ RightModule B :=
  tensorRight N

namespace InternalHom

/-! The first layer records source-order currying through ReasLib's right internal-Hom owner. -/

variable (H : RightInternalHom C)

/-- The ambient right internal-Hom functor, right adjoint to tensoring on the right by `X`. -/
noncomputable abbrev ambient (X : C) : C ⥤ C := H.hom.obj (op X)

/-- Source-order currying in the chosen ambient right internal Hom. -/
noncomputable abbrev ambientHomEquiv (X W Y : C) :
    (W ⊗ X ⟶ Y) ≃ (W ⟶ (ambient H X).obj Y) :=
  H.homEquiv X W Y

/-- Evaluation for source-order ambient internal Hom. -/
noncomputable abbrev ambientEvaluation (X Y : C) :
    (ambient H X).obj Y ⊗ X ⟶ Y := H.ev X Y

variable (N : Bimod A B)

/-- Precomposition with the right `B`-action on `N`. -/
noncomputable def preAction (L : RightModule B) :
    (ambient H N.X).obj L.X ⟶ (ambient H (N.X ⊗ B.X)).obj L.X :=
  ambientHomEquiv H (N.X ⊗ B.X) _ _
    (((ambient H N.X).obj L.X ◁ N.actRight) ≫ ambientEvaluation H N.X L.X)

/-- Postcomposition with the right `B`-action on `L`. -/
noncomputable def postAction (L : RightModule B) :
    (ambient H N.X).obj L.X ⟶ (ambient H (N.X ⊗ B.X)).obj L.X :=
  ambientHomEquiv H (N.X ⊗ B.X) _ _
    ((α_ ((ambient H N.X).obj L.X) N.X B.X).inv ≫
      (ambientEvaluation H N.X L.X ▷ B.X) ≫ L.actRight)

/-- The object of right `B`-linear maps from `N` to `L`. -/
@[stacks 0FR6 "relative internal Hom object"]
noncomputable abbrev carrier (L : RightModule B) : C :=
  equalizer (preAction H N L) (postAction H N L)

/-- The inclusion of right `B`-linear maps into the ambient internal Hom. -/
noncomputable abbrev inclusion (L : RightModule B) :
    carrier H N L ⟶ (ambient H N.X).obj L.X :=
  equalizer.ι (preAction H N L) (postAction H N L)

/-- Evaluation of a right `B`-linear internal map. -/
noncomputable def evaluation (L : RightModule B) : carrier H N L ⊗ N.X ⟶ L.X :=
  (inclusion H N L ▷ N.X) ≫ ambientEvaluation H N.X L.X

/-- The unlifted right `A`-action on the relative internal Hom. -/
noncomputable def actToAmbient (L : RightModule B) :
    carrier H N L ⊗ A.X ⟶ (ambient H N.X).obj L.X :=
  ambientHomEquiv H N.X _ _
    ((α_ (carrier H N L) A.X N.X).hom ≫
      (carrier H N L ◁ N.actLeft) ≫ evaluation H N L)

/-- The unlifted `A`-action preserves right `B`-linearity. -/
theorem actToAmbient_condition (L : RightModule B) :
    actToAmbient H N L ≫ preAction H N L =
      actToAmbient H N L ≫ postAction H N L := sorry

/-- The right `A`-action on `Hom_B(N, L)`. -/
noncomputable def actRight (L : RightModule B) : carrier H N L ⊗ A.X ⟶ carrier H N L :=
  equalizer.lift (actToAmbient H N L) (actToAmbient_condition H N L)

/-- The relative internal Hom as a right `A`-module. -/
@[stacks 0FR6 "relative internal Hom module"]
noncomputable def obj (L : RightModule B) : RightModule A where
  X := carrier H N L
  actLeft := (λ_ (carrier H N L)).hom
  actRight := actRight H N L
  one_actLeft := sorry
  left_assoc := sorry
  actRight_one := sorry
  right_assoc := sorry
  middle_assoc := sorry

/-- Ambient postcomposition sends right `B`-linear maps to right `B`-linear maps. -/
theorem mapToAmbient_condition {L L' : RightModule B} (f : L ⟶ L') :
    (inclusion H N L ≫ (ambient H N.X).map f.hom) ≫ preAction H N L' =
      (inclusion H N L ≫ (ambient H N.X).map f.hom) ≫ postAction H N L' := sorry

/-- The carrier map induced by a morphism of right `B`-modules. -/
noncomputable def mapHom {L L' : RightModule B} (f : L ⟶ L') :
    carrier H N L ⟶ carrier H N L' :=
  equalizer.lift (inclusion H N L ≫ (ambient H N.X).map f.hom)
    (mapToAmbient_condition H N f)

/-- Postcomposition by a right `B`-module map is a right `A`-module map on internal Homs. -/
noncomputable def map {L L' : RightModule B} (f : L ⟶ L') :
    obj H N L ⟶ obj H N L' where
  hom := mapHom H N f
  left_act_hom := sorry
  right_act_hom := sorry

/-- Relative internal Hom with fixed bimodule source, functorial in the target module. -/
@[stacks 0FR6 "relative internal Hom functor"]
noncomputable def functor : RightModule B ⥤ RightModule A where
  obj := obj H N
  map := map H N
  map_id := sorry
  map_comp := sorry

/-- The carrier of the relative internal-Hom module is its defining equalizer. -/
@[simp]
theorem obj_X (L : RightModule B) : (obj H N L).X = carrier H N L := sorry

/-- The internal-Hom functor evaluates to the explicit relative internal-Hom module. -/
@[simp]
theorem functor_obj (L : RightModule B) : (functor H N).obj L = obj H N L := sorry

/-- The underlying map of internal-Hom postcomposition is the canonical equalizer lift. -/
@[simp]
theorem map_hom {L L' : RightModule B} (f : L ⟶ L') :
    (map H N f).hom = mapHom H N f := sorry

/-- Currying a map out of the balanced tensor product before imposing `B`-linearity. -/
noncomputable def curryToAmbient (M : RightModule A) (L : RightModule B)
    (f : (tensorWith N).obj M ⟶ L) : M.X ⟶ (ambient H N.X).obj L.X :=
  ambientHomEquiv H N.X _ _
    (coequalizer.π (M.actRight ▷ N.X)
      ((α_ M.X A.X N.X).hom ≫ (M.X ◁ N.actLeft)) ≫ f.hom)

/-- Currying a balanced right `B`-linear map lands in the defining equalizer. -/
theorem curryToAmbient_condition (M : RightModule A) (L : RightModule B)
    (f : (tensorWith N).obj M ⟶ L) :
    curryToAmbient H N M L f ≫ preAction H N L =
      curryToAmbient H N M L f ≫ postAction H N L := sorry

/-- The forward tensor/internal-Hom transpose. -/
noncomputable def curry (M : RightModule A) (L : RightModule B)
    (f : (tensorWith N).obj M ⟶ L) : M ⟶ obj H N L where
  hom := equalizer.lift (curryToAmbient H N M L f) (curryToAmbient_condition H N M L f)
  left_act_hom := sorry
  right_act_hom := sorry

/-- Evaluation after a map into relative internal Hom, before balancing over `A`. -/
noncomputable def uncurryFromTensor (M : RightModule A) (L : RightModule B)
    (f : M ⟶ obj H N L) : M.X ⊗ N.X ⟶ L.X :=
  (f.hom ▷ N.X) ≫ evaluation H N L

/-- Evaluation of an `A`-linear map is balanced over `A`. -/
theorem uncurryFromTensor_condition (M : RightModule A) (L : RightModule B)
    (f : M ⟶ obj H N L) :
    (M.actRight ▷ N.X) ≫ uncurryFromTensor H N M L f =
      ((α_ M.X A.X N.X).hom ≫ (M.X ◁ N.actLeft)) ≫
        uncurryFromTensor H N M L f := sorry

/-- The inverse tensor/internal-Hom transpose. -/
noncomputable def uncurry (M : RightModule A) (L : RightModule B)
    (f : M ⟶ obj H N L) : (tensorWith N).obj M ⟶ L where
  hom := coequalizer.desc (uncurryFromTensor H N M L f)
    (uncurryFromTensor_condition H N M L f)
  left_act_hom := sorry
  right_act_hom := sorry

/-- Lemma 24.8.2 (0FR6), generic Hom-set form: balanced tensoring with `N` is represented by
the relative internal-Hom functor. -/
@[stacks 0FR6 "relative tensor-Hom equivalence"]
noncomputable def homEquiv (M : RightModule A) (L : RightModule B) :
    ((tensorWith N).obj M ⟶ L) ≃ (M ⟶ (functor H N).obj L) where
  toFun := curry H N M L
  invFun := uncurry H N M L
  left_inv := sorry
  right_inv := sorry

/-- The relative tensor/internal-Hom equivalence is natural in its source and target. -/
noncomputable def coreHomEquiv : Adjunction.CoreHomEquiv (tensorWith N) (functor H N) where
  homEquiv := homEquiv H N
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

/-- Lemma 24.8.2 (0FR6), generic adjunction form: balanced tensoring with `N` is left adjoint
to the explicitly constructed relative internal Hom. -/
@[stacks 0FR6 "relative tensor-Hom adjunction"]
noncomputable def adjunction : tensorWith N ⊣ functor H N :=
  Adjunction.mkOfHomEquiv (coreHomEquiv H N)

/-- A bimodule map induces the corresponding natural transformation of relative tensor
functors. -/
noncomputable def tensorMap {N N' : Bimod A B} (f : N ⟶ N') :
    tensorWith N ⟶ tensorWith N' where
  app M := Bimod.whiskerLeft M f
  naturality := sorry

/-- Precomposition by a bimodule map, obtained as the mate of its relative tensor
transformation. -/
noncomputable def pre {N N' : Bimod A B} (f : N ⟶ N') :
    functor H N' ⟶ functor H N :=
  conjugateEquiv (adjunction H N') (adjunction H N) (tensorMap f)

/-- The relative tensor/Hom equivalence is natural in the right-module source. -/
theorem homEquiv_natural_source (M' M : RightModule A) (L : RightModule B)
    (f : M' ⟶ M) (g : (tensorWith N).obj M ⟶ L) :
    homEquiv H N M' L ((tensorWith N).map f ≫ g) =
      f ≫ homEquiv H N M L g := sorry

/-- The relative tensor/Hom equivalence is natural in the right-module target. -/
theorem homEquiv_natural_target (M : RightModule A) (L L' : RightModule B)
    (f : (tensorWith N).obj M ⟶ L) (g : L ⟶ L') :
    homEquiv H N M L' (f ≫ g) =
      homEquiv H N M L f ≫ (functor H N).map g := sorry

/-- The relative tensor/Hom equivalence is natural in the bimodule variable. -/
theorem homEquiv_natural_bimodule {N N' : Bimod A B} (f : N ⟶ N')
    (M : RightModule A) (L : RightModule B) (g : (tensorWith N').obj M ⟶ L) :
    homEquiv H N M L ((tensorMap f).app M ≫ g) =
      homEquiv H N' M L g ≫ (pre H f).app L := sorry

end InternalHom

namespace InternalHom

variable (H : RightInternalHom C) (M : RightModule A) (N : Bimod A B)

/-- The balanced associator is natural in the right module tensored on the left. -/
theorem tensorAssocNatIso_naturality
    {P Q : RightModule (Mon.trivial C)} (f : P ⟶ Q) :
    (tensorWith M ⋙ tensorWith N).map f ≫ (Bimod.associatorBimod Q M N).hom =
      (Bimod.associatorBimod P M N).hom ≫
        (tensorWith (M.tensorBimod N)).map f := sorry

/-- Associativity of balanced tensor product, promoted to a natural isomorphism of functors. -/
noncomputable def tensorAssocNatIso :
    tensorWith M ⋙ tensorWith N ≅ tensorWith (M.tensorBimod N) :=
  NatIso.ofComponents (fun P ↦ Bimod.associatorBimod P M N)
    (fun f ↦ tensorAssocNatIso_naturality M N f)

/-- The composite tensor/internal-Hom adjunction, transported across the balanced associator. -/
noncomputable def compositeAdjunction :
    tensorWith (M.tensorBimod N) ⊣ functor H N ⋙ functor H M :=
  ((adjunction H M).comp (adjunction H N)).ofNatIsoLeft (tensorAssocNatIso M N)

/-- Lemma 24.8.2 (0FR6), generic internal-Hom form: internal Hom out of a balanced tensor
product is naturally the iterated relative internal Hom. -/
@[stacks 0FR6 "relative internal-Hom currying"]
noncomputable def tensorNatIso :
    functor H (M.tensorBimod N) ≅ functor H N ⋙ functor H M :=
  Adjunction.rightAdjointUniq (adjunction H (M.tensorBimod N))
    (compositeAdjunction H M N)

/-- The objectwise relative internal-Hom currying isomorphism. -/
@[stacks 0FR6 "relative internal-Hom object currying"]
noncomputable abbrev tensorIso (L : RightModule B) :
    (functor H (M.tensorBimod N)).obj L ≅
      (functor H M).obj ((functor H N).obj L) :=
  (tensorNatIso H M N).app L

/-- Internal-Hom currying is natural contravariantly in the right `A`-module. -/
theorem tensorIso_natural_source {M M' : RightModule A} (f : M ⟶ M')
    (N : Bimod A B) (L : RightModule B) :
    (tensorIso H M' N L).hom ≫ (pre H f).app ((functor H N).obj L) =
      (pre H (Bimod.whiskerRight f N)).app L ≫ (tensorIso H M N L).hom := sorry

/-- Internal-Hom currying is natural contravariantly in the bimodule. -/
theorem tensorIso_natural_bimodule (M : RightModule A) {N N' : Bimod A B}
    (f : N ⟶ N') (L : RightModule B) :
    (tensorIso H M N' L).hom ≫ (functor H M).map ((pre H f).app L) =
      (pre H (Bimod.whiskerLeft M f)).app L ≫ (tensorIso H M N L).hom := sorry

/-- Internal-Hom currying is natural covariantly in the right `B`-module target. -/
theorem tensorIso_natural_target (M : RightModule A) (N : Bimod A B)
    {L L' : RightModule B} (f : L ⟶ L') :
    (functor H (M.tensorBimod N)).map f ≫ (tensorIso H M N L').hom =
      (tensorIso H M N L).hom ≫ (functor H M).map ((functor H N).map f) := sorry

end InternalHom

end CategoryTheory.Bimod

end
