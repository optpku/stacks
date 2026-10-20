module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of a site at a set-valued presheaf

The localization site `C / G` is the opposite category of elements of `G`, equipped with the
restricted topology of the elements projection. Sheafification of `G` induces a relocalization
functor whose sheaf pushforward identifies `Sh(C / G)` with the localization of `Sh(C)` at `G#`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u z z'

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- The projection `j : C / G ⥤ C` from the opposite category of elements of a type-valued
presheaf. -/
abbrev localizationForget (G : Cᵒᵖ ⥤ Type (max w v)) : G.Elementsᵒᵖ ⥤ C :=
  (CategoryOfElements.π G).leftOp

/-- The localization site `C / G` is the opposite category of elements of `G` with the
restricted topology of `localizationForget`. -/
abbrev localizationSite (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ Type (max w v)) :
    GrothendieckTopology G.Elementsᵒᵖ :=
  (localizationForget G).restrictedTopology J

/-- A sieve covers on `C / G` exactly when its image under `localizationForget` covers in `J`. -/
theorem mem_localizationSite_iff (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ Type (max w v))
    {X : G.Elementsᵒᵖ} {S : Sieve X} :
    S ∈ localizationSite J G X ↔
      S.functorPushforward (localizationForget G) ∈ J ((localizationForget G).obj X) :=
  sorry

/-- The elements projection is continuous for `localizationSite`. -/
instance localizationForget_isContinuous (J : GrothendieckTopology C)
    (G : Cᵒᵖ ⥤ Type (max w v)) :
    Functor.IsContinuous (localizationForget G) (localizationSite J G) J :=
  sorry

/-- The elements projection is cocontinuous for `localizationSite`. -/
instance localizationForget_isCocontinuous (J : GrothendieckTopology C)
    (G : Cᵒᵖ ⥤ Type (max w v)) :
    Functor.IsCocontinuous (localizationForget G) (localizationSite J G) J :=
  sorry

/-- Fibre products on `C` yield fibre products on `C / G`. -/
instance hasPullbacks_elementsOp (G : Cᵒᵖ ⥤ Type (max w v)) [HasPullbacks C] :
    HasPullbacks G.Elementsᵒᵖ :=
  sorry

/-- Equalizers on `C` yield equalizers on `C / G`. -/
instance hasEqualizers_elementsOp (G : Cᵒᵖ ⥤ Type (max w v)) [HasEqualizers C] :
    HasEqualizers G.Elementsᵒᵖ :=
  sorry

variable (J : GrothendieckTopology C)

/-- Inverse image along `j : C / G ⥤ C`. -/
abbrev elementsOpInverseImage (G : Cᵒᵖ ⥤ Type (max w v)) (A : Type z) [Category.{z'} A] :
    Sheaf J A ⥤ Sheaf (localizationSite J G) A :=
  (localizationForget G).sheafPushforwardContinuous A (localizationSite J G) J

variable [HasWeakSheafify J (Type (max w v))]

/-- The site functor `C / G ⥤ C / G#` induced by the sheafification unit of `G`. -/
def sheafificationRelocalization (G : Cᵒᵖ ⥤ Type (max w v)) :
    G.Elementsᵒᵖ ⥤ ((presheafToSheaf J (Type (max w v))).obj G).obj.Elementsᵒᵖ :=
  (CategoryOfElements.map (toSheafify J G)).op

/-- Relocalization along sheafification commutes with the projections to `C`. -/
theorem sheafificationRelocalization_comp_projection (G : Cᵒᵖ ⥤ Type (max w v)) :
    sheafificationRelocalization J G ⋙
        localizationForget ((presheafToSheaf J (Type (max w v))).obj G).obj =
      localizationForget G :=
  sorry

/-- Sheafification relocalization is continuous for the two localization topologies. -/
instance sheafificationRelocalization_isContinuous (G : Cᵒᵖ ⥤ Type (max w v)) :
    Functor.IsContinuous (sheafificationRelocalization J G)
      (localizationSite J G)
      (localizationSite J ((presheafToSheaf J (Type (max w v))).obj G).obj) :=
  sorry

/-- Sheafification relocalization is cocontinuous for the two localization topologies. -/
instance sheafificationRelocalization_isCocontinuous (G : Cᵒᵖ ⥤ Type (max w v)) :
    Functor.IsCocontinuous (sheafificationRelocalization J G)
      (localizationSite J G)
      (localizationSite J ((presheafToSheaf J (Type (max w v))).obj G).obj) :=
  sorry

/-- Sheaf pushforward along sheafification relocalization is an equivalence, so
`Sh(C / G)` identifies with the localization of `Sh(C)` at `G#`. -/
instance sheafificationRelocalization_sheafPushforward_isEquivalence
    (G : Cᵒᵖ ⥤ Type (max w v)) :
    ((sheafificationRelocalization J G).sheafPushforwardContinuous (Type (max w v))
        (localizationSite J G)
        (localizationSite J
          ((presheafToSheaf J (Type (max w v))).obj G).obj)).IsEquivalence :=
  sorry

end CategoryTheory.Presheaf
