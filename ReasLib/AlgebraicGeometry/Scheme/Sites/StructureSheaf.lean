/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic

/-!
# Structure sheaves on the standard scheme sites

This module constructs the global-sections presheaf for a scheme-valued realization functor
and bundles its standard big, small étale, and small Zariski specializations as ring sheaves
and ringed sites.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Site

variable {C : Type w} [Category.{v} C]

/-- The ring presheaf obtained by taking global sections of a scheme-valued functor. -/
abbrev structurePresheaf (F : C ⥤ Scheme.{u}) : Cᵒᵖ ⥤ RingCat.{u} :=
  F.op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat

/-- The value of `structurePresheaf F` at `U` is the global-sections ring of `F.obj U`. -/
theorem structurePresheaf_obj (F : C ⥤ Scheme.{u}) (U : C) :
    (structurePresheaf F).obj (op U) = RingCat.of Γ(F.obj U, ⊤) := sorry

/-- Restriction in `structurePresheaf F` is the map on global sections induced by `F`. -/
theorem structurePresheaf_map (F : C ⥤ Scheme.{u}) {U V : C} (g : U ⟶ V) :
    (structurePresheaf F).map g.op = RingCat.ofHom (F.map g).appTop.hom := sorry

end AlgebraicGeometry.Scheme.Site

namespace AlgebraicGeometry.StandardTopology.Big

/-- The global-sections presheaf on the big `τ`-site of `S` satisfies the sheaf condition. -/
theorem structurePresheaf_isSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Presheaf.IsSheaf (τ.overTopology S)
      (Scheme.Site.structurePresheaf (Over.forget S)) := sorry

/-- The structure sheaf on the big `τ`-site of `S`. -/
noncomputable def structureSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Sheaf (τ.overTopology S) RingCat.{u} :=
  ⟨Scheme.Site.structurePresheaf (Over.forget S), structurePresheaf_isSheaf τ S⟩

/-- On `U ⟶ S`, the big-site structure sheaf has value `Γ(U, 𝒪_U)`. -/
theorem structureSheaf_obj (τ : StandardTopology) (S : Scheme.{u}) (U : Over S) :
    (structureSheaf τ S).obj.obj (op U) = RingCat.of Γ(U.left, ⊤) := sorry

/-- Restriction in the big-site structure sheaf is pullback of global functions. -/
theorem structureSheaf_map (τ : StandardTopology) (S : Scheme.{u})
    {U V : Over S} (g : U ⟶ V) :
    (structureSheaf τ S).obj.map g.op = RingCat.ofHom g.left.appTop.hom := sorry

/-- The big `τ`-site of `S`, equipped with its structure sheaf. -/
abbrev ringedSite (τ : StandardTopology) (S : Scheme.{u}) : RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (τ.overTopology S) (structureSheaf τ S)

/-- The structure sheaf of `ringedSite τ S` is the global-sections sheaf. -/
theorem ringedSite_structureSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    (ringedSite τ S).structureSheaf = structureSheaf τ S := sorry

end AlgebraicGeometry.StandardTopology.Big

namespace AlgebraicGeometry.Scheme.Etale.Small

/-- The global-sections presheaf on the small étale site is a sheaf. -/
theorem structurePresheaf_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf S.smallEtaleTopology
      (Scheme.Site.structurePresheaf (Scheme.smallEtaleToScheme S)) := sorry

/-- The structure sheaf on the small étale site of `S`. -/
noncomputable def structureSheaf (S : Scheme.{u}) :
    Sheaf S.smallEtaleTopology RingCat.{u} :=
  ⟨Scheme.Site.structurePresheaf (Scheme.smallEtaleToScheme S),
    structurePresheaf_isSheaf S⟩

/-- On `U ⟶ S`, the small-étale structure sheaf has value `Γ(U, 𝒪_U)`. -/
theorem structureSheaf_obj (S : Scheme.{u}) (U : S.Etale) :
    (structureSheaf S).obj.obj (op U) = RingCat.of Γ(U.left, ⊤) := sorry

/-- Restriction in the small-étale structure sheaf is pullback of global functions. -/
theorem structureSheaf_map (S : Scheme.{u}) {U V : S.Etale} (g : U ⟶ V) :
    (structureSheaf S).obj.map g.op = RingCat.ofHom g.left.appTop.hom := sorry

/-- The small étale site of `S`, equipped with its structure sheaf. -/
abbrev ringedSite (S : Scheme.{u}) : RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf S.smallEtaleTopology (structureSheaf S)

/-- The structure sheaf of the small-étale ringed site is the global-sections sheaf. -/
theorem ringedSite_structureSheaf (S : Scheme.{u}) :
    (ringedSite S).structureSheaf = structureSheaf S := sorry

end AlgebraicGeometry.Scheme.Etale.Small

namespace AlgebraicGeometry.Scheme.Zariski.Small

/-- The global-sections presheaf on the small Zariski site is a sheaf. -/
theorem structurePresheaf_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf S.smallZariskiTopology
      (Scheme.Site.structurePresheaf (Scheme.smallZariskiToScheme S)) := sorry

/-- The structure sheaf on the small Zariski site of `S`. -/
noncomputable def structureSheaf (S : Scheme.{u}) :
    Sheaf S.smallZariskiTopology RingCat.{u} :=
  ⟨Scheme.Site.structurePresheaf (Scheme.smallZariskiToScheme S),
    structurePresheaf_isSheaf S⟩

/-- On `U ⟶ S`, the small-Zariski structure sheaf has value `Γ(U, 𝒪_U)`. -/
theorem structureSheaf_obj (S : Scheme.{u}) (U : S.smallZariskiSite) :
    (structureSheaf S).obj.obj (op U) = RingCat.of Γ(U.left, ⊤) := sorry

/-- Restriction in the small-Zariski structure sheaf is pullback of global functions. -/
theorem structureSheaf_map (S : Scheme.{u})
    {U V : S.smallZariskiSite} (g : U ⟶ V) :
    (structureSheaf S).obj.map g.op = RingCat.ofHom g.left.appTop.hom := sorry

/-- The small Zariski site of `S`, equipped with its structure sheaf. -/
abbrev ringedSite (S : Scheme.{u}) : RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf S.smallZariskiTopology (structureSheaf S)

/-- The structure sheaf of the small-Zariski ringed site is the global-sections sheaf. -/
theorem ringedSite_structureSheaf (S : Scheme.{u}) :
    (ringedSite S).structureSheaf = structureSheaf S := sorry

end AlgebraicGeometry.Scheme.Zariski.Small
