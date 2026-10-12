/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Category
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.InternalHom

/-!
# Reflected tensor products of coherent reflexive module sheaves

On an integral locally Noetherian scheme, reflection of the ambient tensor product equips
coherent reflexive module sheaves with a symmetric closed monoidal structure.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- The module sheaf underlying a coherent reflexive module sheaf. -/
abbrev reflexiveCohUnderlying (ℱ : ReflexiveCoh X) : X.Modules :=
  (reflexiveCohForget X).obj ℱ

/-- The module sheaf underlying a coherent reflexive module sheaf is coherent. -/
instance instIsCoherentReflexiveCohUnderlying (ℱ : ReflexiveCoh X) :
    (reflexiveCohUnderlying X ℱ).IsCoherent :=
  ℱ.obj.property

/-- The module sheaf underlying a coherent reflexive module sheaf is reflexive. -/
instance instIsReflexiveReflexiveCohUnderlying (ℱ : ReflexiveCoh X) :
    IsReflexive (reflexiveCohUnderlying X ℱ) :=
  ℱ.property

/-- A morphism of underlying module sheaves regarded as a morphism of coherent reflexive
module sheaves. -/
def reflexiveCohHomMk {ℱ 𝒢 : ReflexiveCoh X}
    (f : reflexiveCohUnderlying X ℱ ⟶ reflexiveCohUnderlying X 𝒢) : ℱ ⟶ 𝒢 :=
  ObjectProperty.homMk (ObjectProperty.homMk f)

/-- A morphism from a coherent module sheaf to a coherent reflexive module sheaf extends
canonically across the reflexive hull of its source. -/
noncomputable def reflexiveHullDesc {ℱ 𝒢 : X.Modules}
    [ℱ.IsCoherent] [𝒢.IsCoherent] [IsReflexive 𝒢] (f : ℱ ⟶ 𝒢) :
    reflexiveHull ℱ ⟶ 𝒢 :=
  reflexiveHullMap f ≫ inv (toReflexiveHull 𝒢)

/-- The reflexive tensor product is the reflexive hull of the ambient tensor product. -/
noncomputable def reflexiveTensor (ℱ 𝒢 : ReflexiveCoh X) : ReflexiveCoh X := by
  exact
    ⟨⟨reflexiveHull (reflexiveCohUnderlying X ℱ ⊗ reflexiveCohUnderlying X 𝒢),
        inferInstance⟩,
      inferInstance⟩

/-- The map on reflexive tensor products induced by two morphisms. -/
noncomputable def reflexiveTensorMap {ℱ ℱ' 𝒢 𝒢' : ReflexiveCoh X}
    (f : ℱ ⟶ ℱ') (g : 𝒢 ⟶ 𝒢') : reflexiveTensor X ℱ 𝒢 ⟶ reflexiveTensor X ℱ' 𝒢' :=
  reflexiveCohHomMk X (reflexiveHullMap
    ((reflexiveCohForget X).map f ⊗ₘ (reflexiveCohForget X).map g))

/-- The structure sheaf as a coherent reflexive module sheaf. -/
noncomputable def reflexiveCohTensorUnit : ReflexiveCoh X :=
  ⟨⟨𝟙_ X.Modules, inferInstance⟩, inferInstance⟩

/-- The forward associator morphism for the reflexive tensor product. -/
noncomputable def reflexiveAssociatorHom (ℱ 𝒢 ℋ : ReflexiveCoh X) :
    reflexiveTensor X (reflexiveTensor X ℱ 𝒢) ℋ ⟶
      reflexiveTensor X ℱ (reflexiveTensor X 𝒢 ℋ) := by
  let F := reflexiveCohUnderlying X ℱ
  let G := reflexiveCohUnderlying X 𝒢
  let H := reflexiveCohUnderlying X ℋ
  let T := reflexiveCohUnderlying X (reflexiveTensor X ℱ (reflexiveTensor X 𝒢 ℋ))
  let core : (F ⊗ G) ⊗ H ⟶ T :=
    (α_ F G H).hom ≫
      (F ◁ toReflexiveHull (G ⊗ H)) ≫
      toReflexiveHull (F ⊗ reflexiveHull (G ⊗ H))
  let curried : F ⊗ G ⟶ internalHom H T :=
    MonoidalClosed.curry ((β_ H (F ⊗ G)).hom ≫ core)
  let inner : reflexiveHull (F ⊗ G) ⟶ internalHom H T :=
    reflexiveHullDesc X curried
  let middle : reflexiveHull (F ⊗ G) ⊗ H ⟶ T :=
    (β_ (reflexiveHull (F ⊗ G)) H).hom ≫ MonoidalClosed.uncurry inner
  exact reflexiveCohHomMk X (reflexiveHullDesc X middle)

/-- The inverse associator morphism for the reflexive tensor product. -/
noncomputable def reflexiveAssociatorInv (ℱ 𝒢 ℋ : ReflexiveCoh X) :
    reflexiveTensor X ℱ (reflexiveTensor X 𝒢 ℋ) ⟶
      reflexiveTensor X (reflexiveTensor X ℱ 𝒢) ℋ := by
  let F := reflexiveCohUnderlying X ℱ
  let G := reflexiveCohUnderlying X 𝒢
  let H := reflexiveCohUnderlying X ℋ
  let S := reflexiveCohUnderlying X (reflexiveTensor X (reflexiveTensor X ℱ 𝒢) ℋ)
  let core : F ⊗ (G ⊗ H) ⟶ S :=
    (α_ F G H).inv ≫
      (toReflexiveHull (F ⊗ G) ▷ H) ≫
      toReflexiveHull (reflexiveHull (F ⊗ G) ⊗ H)
  let curried : G ⊗ H ⟶ internalHom F S := MonoidalClosed.curry core
  let inner : reflexiveHull (G ⊗ H) ⟶ internalHom F S :=
    reflexiveHullDesc X curried
  exact reflexiveCohHomMk X (reflexiveHullDesc X (MonoidalClosed.uncurry inner))

/-- The forward left-unitor morphism for the reflexive tensor product. -/
noncomputable def reflexiveLeftUnitorHom (ℱ : ReflexiveCoh X) :
    reflexiveTensor X (reflexiveCohTensorUnit X) ℱ ⟶ ℱ := by
  exact reflexiveCohHomMk X (reflexiveHullDesc X (λ_ (reflexiveCohUnderlying X ℱ)).hom)

/-- The inverse left-unitor morphism for the reflexive tensor product. -/
noncomputable def reflexiveLeftUnitorInv (ℱ : ReflexiveCoh X) :
    ℱ ⟶ reflexiveTensor X (reflexiveCohTensorUnit X) ℱ :=
  reflexiveCohHomMk X ((λ_ (reflexiveCohUnderlying X ℱ)).inv ≫
    toReflexiveHull (𝟙_ X.Modules ⊗ reflexiveCohUnderlying X ℱ))

/-- The forward right-unitor morphism for the reflexive tensor product. -/
noncomputable def reflexiveRightUnitorHom (ℱ : ReflexiveCoh X) :
    reflexiveTensor X ℱ (reflexiveCohTensorUnit X) ⟶ ℱ := by
  exact reflexiveCohHomMk X (reflexiveHullDesc X (ρ_ (reflexiveCohUnderlying X ℱ)).hom)

/-- The inverse right-unitor morphism for the reflexive tensor product. -/
noncomputable def reflexiveRightUnitorInv (ℱ : ReflexiveCoh X) :
    ℱ ⟶ reflexiveTensor X ℱ (reflexiveCohTensorUnit X) :=
  reflexiveCohHomMk X ((ρ_ (reflexiveCohUnderlying X ℱ)).inv ≫
    toReflexiveHull (reflexiveCohUnderlying X ℱ ⊗ 𝟙_ X.Modules))

/-- Reflexive tensor equips coherent reflexive modules with a monoidal structure. -/
noncomputable instance instMonoidalCategoryReflexiveCoh :
    MonoidalCategory (ReflexiveCoh X) := by
  refine
    { tensorObj := reflexiveTensor X
      whiskerLeft := fun ℱ _ _ g ↦ reflexiveTensorMap X (𝟙 ℱ) g
      whiskerRight := fun {_ _} f 𝒢 ↦ reflexiveTensorMap X f (𝟙 𝒢)
      tensorHom := reflexiveTensorMap X
      tensorUnit := reflexiveCohTensorUnit X
      associator := fun ℱ 𝒢 ℋ ↦
        { hom := reflexiveAssociatorHom X ℱ 𝒢 ℋ
          inv := reflexiveAssociatorInv X ℱ 𝒢 ℋ
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      leftUnitor := fun ℱ ↦
        { hom := reflexiveLeftUnitorHom X ℱ
          inv := reflexiveLeftUnitorInv X ℱ
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      rightUnitor := fun ℱ ↦
        { hom := reflexiveRightUnitorHom X ℱ
          inv := reflexiveRightUnitorInv X ℱ
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      tensorHom_def := ?_
      id_tensorHom_id := ?_
      tensorHom_comp_tensorHom := ?_
      whiskerLeft_id := ?_
      id_whiskerRight := ?_
      associator_naturality := ?_
      leftUnitor_naturality := ?_
      rightUnitor_naturality := ?_
      pentagon := ?_
      triangle := ?_ }
  all_goals sorry

/-- Reflexive tensor is symmetric. -/
noncomputable instance instSymmetricCategoryReflexiveCoh :
    SymmetricCategory (ReflexiveCoh X) := by
  refine
    { braiding := fun ℱ 𝒢 ↦ ?_
      braiding_naturality_right := ?_
      braiding_naturality_left := ?_
      hexagon_forward := ?_
      hexagon_reverse := ?_
      symmetry := ?_ }
  · let e :
        reflexiveCohUnderlying X (reflexiveTensor X ℱ 𝒢) ≅
          reflexiveCohUnderlying X (reflexiveTensor X 𝒢 ℱ) :=
      (reflexiveHullFunctor X).mapIso
        (β_ (reflexiveCohUnderlying X ℱ) (reflexiveCohUnderlying X 𝒢))
    exact ObjectProperty.isoMk (reflexiveCohProperty X)
      (ObjectProperty.isoMk (SheafOfModules.isCoherent X.ringCatSheaf) e)
  all_goals sorry

/-- Ambient internal Hom restricts to an endofunctor on coherent reflexive modules. -/
noncomputable def reflexiveCohInternalHom (ℱ : ReflexiveCoh X) :
    ReflexiveCoh X ⥤ ReflexiveCoh X := by
  let H : ReflexiveCoh X ⥤ X.Modules :=
    reflexiveCohForget X ⋙ ihom (reflexiveCohUnderlying X ℱ)
  let HCoh : ReflexiveCoh X ⥤ RingedSpace.Coh X.toRingedSpace :=
    ObjectProperty.lift (SheafOfModules.isCoherent X.ringCatSheaf) H
      (fun 𝒢 ↦ by
        change (internalHom (reflexiveCohUnderlying X ℱ)
          (reflexiveCohUnderlying X 𝒢)).IsCoherent
        infer_instance)
  exact ObjectProperty.lift (reflexiveCohProperty X) HCoh
    (fun 𝒢 ↦ by
      change IsReflexive (internalHom (reflexiveCohUnderlying X ℱ)
        (reflexiveCohUnderlying X 𝒢))
      infer_instance)

/-- Tensoring on the left is adjoint to coherent-reflexive internal Hom. -/
noncomputable def reflexiveTensorInternalHomAdjunction (ℱ : ReflexiveCoh X) :
    tensorLeft ℱ ⊣ reflexiveCohInternalHom X ℱ := by
  refine Adjunction.mkOfHomEquiv
    { homEquiv := fun 𝒢 ℋ ↦
        { toFun := fun f ↦ reflexiveCohHomMk X (MonoidalClosed.curry
              (toReflexiveHull
                  (reflexiveCohUnderlying X ℱ ⊗ reflexiveCohUnderlying X 𝒢) ≫
                (reflexiveCohForget X).map f))
          invFun := fun g ↦ by
            exact reflexiveCohHomMk X (reflexiveHullDesc X
              (MonoidalClosed.uncurry ((reflexiveCohForget X).map g)))
          left_inv := ?_
          right_inv := ?_ }
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  all_goals sorry

/-- The tensor--internal-Hom adjunction as a natural equivalence of hom sets. -/
noncomputable def reflexiveTensorHomEquiv (ℱ 𝒢 ℋ : ReflexiveCoh X) :
    (ℱ ⊗ 𝒢 ⟶ ℋ) ≃ (ℱ ⟶ (reflexiveCohInternalHom X 𝒢).obj ℋ) :=
  ((β_ ℱ 𝒢).homCongr (Iso.refl ℋ)).trans
    ((reflexiveTensorInternalHomAdjunction X 𝒢).homEquiv ℱ ℋ)

/-- Coherent reflexive modules form a closed monoidal category. -/
noncomputable instance instMonoidalClosedReflexiveCoh : MonoidalClosed (ReflexiveCoh X) where
  closed ℱ :=
    { rightAdj := reflexiveCohInternalHom X ℱ
      adj := reflexiveTensorInternalHomAdjunction X ℱ }

/-- The dual of a coherent reflexive module is its internal Hom into the tensor unit. -/
noncomputable def reflexiveCohDual (ℱ : ReflexiveCoh X) : ReflexiveCoh X :=
  (reflexiveCohInternalHom X ℱ).obj (reflexiveCohTensorUnit X)

end AlgebraicGeometry.Scheme.Modules
