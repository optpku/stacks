module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Big and small Zariski sites of a scheme

This module provides big and small Zariski site interfaces for a scheme. The
topology owners remain Mathlib's `Scheme.zariskiTopology` and
`Scheme.smallGrothendieckTopology`; this layer gives their slice-site forms and
the canonical functors from open subschemes.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme

section ZariskiSites

variable (S : Scheme.{u})

/-- The underlying category of the big Zariski site of a scheme. -/
abbrev bigZariskiSite := Over S

/-- The big Zariski site of `S` is the slice category `Over S` endowed with the
Zariski topology localized from `Scheme`. -/
@[stacks 020T]
abbrev bigZariskiTopology : GrothendieckTopology S.bigZariskiSite :=
  Scheme.zariskiTopology.over S

/-- The underlying category of the small Zariski site of a scheme. -/
abbrev smallZariskiSite :=
  (IsOpenImmersion : MorphismProperty Scheme.{u}).Over ⊤ S

/-- The small Zariski site of `S` is the full subcategory of `(Sch/S)_{Zar}` on open
immersions, with coverings induced from the big Zariski site. -/
@[stacks 020T]
abbrev smallZariskiTopology : GrothendieckTopology S.smallZariskiSite :=
  S.smallGrothendieckTopology IsOpenImmersion

/-- The big Zariski site of `S` is the localized Zariski topology on `Over S`. -/
theorem bigZariskiTopology_eq_over :
    S.bigZariskiTopology = Scheme.zariskiTopology.over S := sorry

/-- The small Zariski site of `S` carries the induced topology on open immersions over `S`. -/
theorem smallZariskiTopology_eq_small :
    S.smallZariskiTopology = S.smallGrothendieckTopology IsOpenImmersion := sorry

/-- The canonical functor sending an open subset `U ⊆ S` to the corresponding open immersion
`U ⟶ S`, viewed as an object of the small Zariski site of `S`. -/
def smallZariskiOpenFunctor : S.Opens ⥤ S.smallZariskiSite :=
  MorphismProperty.Comma.lift S.restrictFunctor
    (fun U ↦ (Scheme.restrictFunctor_obj_hom S U).symm ▸
      (inferInstance : IsOpenImmersion U.ι))
    (fun _ ↦ trivial)
    (fun _ ↦ trivial)

/-- The structural morphism of `smallZariskiOpenFunctor S` at `U` is the inclusion `U.ι`. -/
@[simp]
theorem smallZariskiOpenFunctor_obj_hom (U : S.Opens) :
    ((smallZariskiOpenFunctor S).obj U).hom = U.ι := sorry

/-- The source scheme of `smallZariskiOpenFunctor S` at `U` is the open subscheme `U`. -/
@[simp]
theorem smallZariskiOpenFunctor_obj_left (U : S.Opens) :
    ((smallZariskiOpenFunctor S).obj U).left = U := sorry

/-- The underlying scheme map of `smallZariskiOpenFunctor S` on an inclusion of opens is
`S.homOfLE`. -/
@[simp]
theorem smallZariskiOpenFunctor_map_left {U V : S.Opens} (i : U ⟶ V) :
    ((smallZariskiOpenFunctor S).map i).left = S.homOfLE i.le := sorry

/-- The canonical forgetful functor from the small Zariski site of `S` to `Over S`. -/
abbrev smallZariskiForget : S.smallZariskiSite ⥤ Over S :=
  MorphismProperty.Over.forget IsOpenImmersion ⊤ S

/-- Forgetting the open-immersion condition after `smallZariskiOpenFunctor S` recovers
`S.restrictFunctor`. -/
theorem smallZariskiOpenFunctor_comp_forget :
    smallZariskiOpenFunctor S ⋙ smallZariskiForget S = S.restrictFunctor := sorry

/-- The canonical forgetful functor from the small Zariski site of `S` to schemes. -/
abbrev smallZariskiToScheme : S.smallZariskiSite ⥤ Scheme :=
  smallZariskiForget S ⋙ Over.forget S

end ZariskiSites

end Scheme
end AlgebraicGeometry
