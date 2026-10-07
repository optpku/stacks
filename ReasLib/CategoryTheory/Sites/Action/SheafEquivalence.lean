module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.Action.JointlySurjective
public import ReasLib.CategoryTheory.Sites.Action.LeftRegular

/-!
# Sheaves on the jointly-surjective action site

This module owns the equivalence between `G`-sets and sheaves for the jointly-surjective topology
on `G`-sets.  Its quasi-inverse is evaluation on the left-regular `G`-set, equipped with the
action induced by right translations.
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe u v

namespace CategoryTheory

namespace Action.SheafEquivalence

section

variable (G : Type u) [Monoid G]

namespace LeftRegular

/-- Pullback along right multiplication by `1` is the identity on left-regular sections. -/
theorem sectionsMapOne
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)) :
    ℱ.obj.map (op (Action.leftRegularRightMul G 1)) =
      𝟙 (ℱ.obj.obj (op (Action.leftRegular G))) := sorry

/-- Pullback along right multiplication reverses the product in the induced left action. -/
theorem sectionsMapMul
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)) (g h : G) :
    ℱ.obj.map (op (Action.leftRegularRightMul G (g * h))) =
      ℱ.obj.map (op (Action.leftRegularRightMul G h)) ≫
        ℱ.obj.map (op (Action.leftRegularRightMul G g)) := sorry

/-- The left action on sections over the left regular `G`-set induced by pullback. -/
instance sectionsMulAction
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)) :
    MulAction G (ℱ.obj.obj (op (Action.leftRegular G))) where
  smul g := ℱ.obj.map (op (Action.leftRegularRightMul G g))
  one_smul := sorry
  mul_smul := sorry

/-- The equivariant map on left-regular sections induced by a sheaf morphism. -/
def sectionsMap
    {ℱ 𝒢 : Sheaf (Action.jointlySurjectiveTopology G) (Type v)} (η : ℱ ⟶ 𝒢) :
    Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G))) ⟶
      Action.ofMulAction G (𝒢.obj.obj (op (Action.leftRegular G))) where
  hom := η.hom.app (op (Action.leftRegular G))
  comm := sorry

/-- The left-regular-sections construction preserves identity morphisms. -/
theorem sectionsFunctor_map_id
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)) :
    sectionsMap G (𝟙 ℱ) =
      𝟙 (Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G)))) := sorry

/-- The left-regular-sections construction preserves composition. -/
theorem sectionsFunctor_map_comp
    {ℱ 𝒢 ℋ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)}
    (η : ℱ ⟶ 𝒢) (θ : 𝒢 ⟶ ℋ) :
    sectionsMap G (η ≫ θ) =
      sectionsMap G η ≫ sectionsMap G θ := sorry

/-- The functor sending a sheaf to its `G`-set of sections on `{}_G G`. -/
def sectionsFunctor :
    Sheaf (Action.jointlySurjectiveTopology G) (Type v) ⥤ Action (Type v) G where
  obj ℱ := Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G)))
  map := sectionsMap G
  map_id := sectionsFunctor_map_id G
  map_comp := sectionsFunctor_map_comp G

/-- Evaluation at `1 ∈ G` identifies sections of a representable sheaf on the left regular
`G`-set with the represented `G`-set. -/
noncomputable def yonedaIso (S : Action (Type u) G) :
    S ≅ (sectionsFunctor G).obj
      ((Action.jointlySurjectiveTopology G).yoneda.obj S) :=
  Action.mkIso
    { hom := ↾fun s : S.V ↦ Action.leftRegularOrbitHom G s
      inv := ↾fun a ↦ a.hom (1 : G)
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- Naturality of the representable left-regular-sections identification. -/
@[reassoc]
theorem yonedaIso_naturality
    {S T : Action (Type u) G} (f : S ⟶ T) :
    f ≫ (yonedaIso G T).hom =
      (yonedaIso G S).hom ≫
        (sectionsFunctor G).map
          ((Action.jointlySurjectiveTopology G).yoneda.map f) := sorry

/-- The singleton orbit cover and the stabilizer-indexed right-translation family impose the
same sheaf condition. -/
theorem singletonCoverIsSheafFor_iff_stabilizerFamily
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v))
    {U : Action (Type u) G} (u : U.V) :
    (Presieve.ofArrows
      (fun _ : PUnit ↦ Action.leftRegular G)
      (fun _ : PUnit ↦ Action.leftRegularOrbitHom G u)).IsSheafFor ℱ.obj ↔
      (Presieve.ofArrows
        (fun _ : { g : G // U.ρ g u = u } ↦ Action.leftRegular G)
        (fun h : { g : G // U.ρ g u = u } ↦
          Action.leftRegularRightMul G h.1 ≫ Action.leftRegularOrbitHom G u)).IsSheafFor
        ℱ.obj := sorry

end LeftRegular

namespace Counit

/-- The explicit presheaf map sending a section to its family of orbit restrictions. -/
noncomputable def toPresheaf :
    sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u) ⟶
      (LeftRegular.sectionsFunctor G ⋙ (Action.jointlySurjectiveTopology G).yoneda) ⋙
        sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u) where
  app ℱ :=
    { app := fun U ↦
        ↾fun s ↦
          { hom := ↾fun u : U.unop.V ↦
              ℱ.obj.map (op (Action.leftRegularOrbitHom G u)) s
            comm := sorry }
      naturality := sorry }
  naturality := sorry

/-- The sheaf-side counit lifted from `Counit.toPresheaf` by full faithfulness. -/
noncomputable def toYoneda :
    𝟭 (Sheaf (Action.jointlySurjectiveTopology G) (Type u)) ⟶
      LeftRegular.sectionsFunctor G ⋙ (Action.jointlySurjectiveTopology G).yoneda :=
  ((fullyFaithfulSheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u)).whiskeringRight
      (Sheaf (Action.jointlySurjectiveTopology G) (Type u))).preimage
    (toPresheaf G)

/-- The presheaf counit on the left regular object is the orbit-map construction. -/
theorem toPresheaf_app_leftRegular_eq
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u))
    (s : ℱ.obj.obj (op (Action.leftRegular G))) :
    (((toPresheaf G).app ℱ).app (op (Action.leftRegular G)) s) =
      Action.leftRegularOrbitHom G s := sorry

/-- The presheaf counit component on the left regular object is bijective. -/
theorem toPresheaf_app_leftRegular_bijective
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u)) :
    Function.Bijective
      (((toPresheaf G).app ℱ).app (op (Action.leftRegular G))) := sorry

/-- The family of orbit maps indexed by points of `U` is a covering family. -/
theorem orbitFamilyCovering
    (U : Action (Type u) G) :
    Sieve.ofArrows (fun _ : U.V ↦ Action.leftRegular G)
      (fun u : U.V ↦ Action.leftRegularOrbitHom G u) ∈
        Action.jointlySurjectiveTopology G U := sorry

/-- Sections agreeing after all orbit restrictions agree globally. -/
theorem eq_of_orbitRestrictions_eq
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u))
    {U : Action (Type u) G} {s₁ s₂ : ℱ.obj.obj (op U)}
    (h : ∀ u : U.V,
      ℱ.obj.map (op (Action.leftRegularOrbitHom G u)) s₁ =
        ℱ.obj.map (op (Action.leftRegularOrbitHom G u)) s₂) :
    s₁ = s₂ := sorry

/-- The explicit presheaf counit commutes with pullback along equivariant maps. -/
theorem toPresheaf_app_eq_comp
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u))
    {U V : Action (Type u) G} (f : U ⟶ V) (s : ℱ.obj.obj (op V)) :
    (((toPresheaf G).app ℱ).app (op U) (ℱ.obj.map f.op s)) =
      f ≫ (((toPresheaf G).app ℱ).app (op V) s) := sorry

/-- The values of an equivariant map form a compatible family on the orbit cover. -/
theorem familyCompatible
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u))
    {U : Action (Type u) G}
    (t : (((Action.jointlySurjectiveTopology G).yoneda.obj
      (Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G))))).obj.obj (op U))) :
    Presieve.Arrows.Compatible ℱ.obj
      (fun u : U.V ↦ Action.leftRegularOrbitHom G u)
      (fun u : U.V ↦ t.hom u) := sorry

/-- The explicit presheaf counit component is bijective on every `G`-set. -/
theorem toPresheaf_app_bijective
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u))
    (U : Action (Type u) G) :
    Function.Bijective (((toPresheaf G).app ℱ).app (op U)) := sorry

/-- Each component of the sheaf-side counit is an isomorphism. -/
theorem toYoneda_app_isIso
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u)) :
    IsIso ((toYoneda G).app ℱ) := sorry

/-- The explicit sheaf-side counit is an isomorphism. -/
noncomputable instance toYoneda_isIso :
    IsIso (toYoneda G) := sorry

/-- The natural isomorphism exhibiting left-regular sections as a quasi-inverse to Yoneda. -/
noncomputable def iso :
    LeftRegular.sectionsFunctor G ⋙ (Action.jointlySurjectiveTopology G).yoneda ≅
      𝟭 (Sheaf (Action.jointlySurjectiveTopology G) (Type u)) :=
  (asIso (toYoneda G)).symm

end Counit

/-- 00W0 (Proposition 7.9.1): the Yoneda functor for the jointly-surjective topology on `G`-sets
is an equivalence, with inverse given by left-regular sections. -/
@[stacks 00W0]
theorem yonedaIsEquivalence :
    Functor.IsEquivalence
      ((Action.jointlySurjectiveTopology G).yoneda :
        Action (Type u) G ⥤ Sheaf (Action.jointlySurjectiveTopology G) (Type u)) := sorry

attribute [instance] yonedaIsEquivalence

/-- The concrete equivalence whose inverse is the left-regular-sections functor. -/
noncomputable def yonedaEquivalence :
    Action (Type u) G ≌ Sheaf (Action.jointlySurjectiveTopology G) (Type u) :=
  CategoryTheory.Equivalence.mk
    ((Action.jointlySurjectiveTopology G).yoneda)
    (LeftRegular.sectionsFunctor G)
    (NatIso.ofComponents (fun S ↦ LeftRegular.yonedaIso G S)
      (fun f ↦ LeftRegular.yonedaIso_naturality G f))
    (Counit.iso G)

/-- The canonical inverse of Yoneda is naturally isomorphic to left-regular sections. -/
noncomputable def yonedaInverseIso :
    (((Action.jointlySurjectiveTopology G).yoneda :
        Action (Type u) G ⥤ Sheaf (Action.jointlySurjectiveTopology G) (Type u)).inv) ≅
      LeftRegular.sectionsFunctor G :=
  Iso.isoInverseOfIsoFunctor
    (G := ((Action.jointlySurjectiveTopology G).yoneda).asEquivalence)
    (G' := yonedaEquivalence G)
    (Iso.refl _)

/-- The objectwise component of the inverse-functor comparison. -/
noncomputable def yonedaInverseObjIso
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u)) :
    ((Action.jointlySurjectiveTopology G).yoneda.inv.obj ℱ) ≅
      (LeftRegular.sectionsFunctor G).obj ℱ :=
  (yonedaInverseIso (G := G)).app ℱ

/-- Naturality of the objectwise comparison between the canonical inverse and left-regular
sections. -/
theorem yonedaInverseObjIso_naturality
    {ℱ 𝒢 : Sheaf (Action.jointlySurjectiveTopology G) (Type u)} (η : ℱ ⟶ 𝒢) :
    ((Action.jointlySurjectiveTopology G).yoneda.inv.map η) ≫
        (yonedaInverseObjIso (G := G) 𝒢).hom =
      (yonedaInverseObjIso (G := G) ℱ).hom ≫
        (LeftRegular.sectionsFunctor G).map η := sorry

end

end Action.SheafEquivalence

end CategoryTheory
