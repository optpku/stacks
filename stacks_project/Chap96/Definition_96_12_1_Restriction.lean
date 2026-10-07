module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf

/-!
# Small-étale restriction of modules on a groupoid fibration

An object `x` of a category fibred in groupoids over `(Sch/S)_fppf` determines a
functor from the small étale site of `U = p(x)` into the total category, by
cartesian lifts of étale neighborhoods. Pushing an `𝒪_X`-module along the
induced comparison of structure sheaves yields the restriction `x* F|_{U_étale}`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.AssociatedModule
open Functor.IsPreFibered

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The morphism in `Over S` associated to an étale neighborhood of `p(x)`. -/
def etaleOverHom {X : GroupoidsOver S} (x : X.total)
    (V' : SmallStandardTopology.etale.site (X.p.obj x).left) :
    Over.mk (V'.hom ≫ (X.p.obj x).hom) ⟶ X.p.obj x :=
  Over.homMk V'.hom

/-- Triangle identity for the `Over S` morphism associated to a map of étale
neighborhoods of `p(x)`. -/
theorem etaleOverHomMap_w {X : GroupoidsOver S} {x : X.total}
    {V' W' : SmallStandardTopology.etale.site (X.p.obj x).left} (f : V' ⟶ W') :
    f.left ≫ (W'.hom ≫ (X.p.obj x).hom) = V'.hom ≫ (X.p.obj x).hom :=
  sorry

/-- The morphism in `Over S` associated to a morphism of étale neighborhoods of
`p(x)`. -/
def etaleOverHomMap {X : GroupoidsOver S} {x : X.total}
    {V' W' : SmallStandardTopology.etale.site (X.p.obj x).left} (f : V' ⟶ W') :
    Over.mk (V'.hom ≫ (X.p.obj x).hom) ⟶ Over.mk (W'.hom ≫ (X.p.obj x).hom) :=
  Over.homMk f.left (etaleOverHomMap_w f)

/-- Compatibility of `etaleOverHom` with morphisms of étale neighborhoods. -/
theorem etaleOverHom_comp {X : GroupoidsOver S} {x : X.total}
    {V' W' : SmallStandardTopology.etale.site (X.p.obj x).left} (f : V' ⟶ W') :
    etaleOverHom x V' = etaleOverHomMap f ≫ etaleOverHom x W' :=
  sorry

/-- The functor from the small étale site of `U = p(x)` to the total category of
`X`, sending an étale neighborhood of `U` to a chosen cartesian lift of `x`. -/
def smallEtaleToTotal {X : GroupoidsOver S} (x : X.total) :
    SmallStandardTopology.etale.site (X.p.obj x).left ⥤ X.total where
  obj V' := pullbackObj (p := X.p) rfl (etaleOverHom x V')
  map {V' W'} f :=
    Functor.IsStronglyCartesian.map (p := X.p) (etaleOverHom x W')
      (pullbackMap (p := X.p) rfl (etaleOverHom x W'))
      (etaleOverHom_comp f)
      (pullbackMap (p := X.p) rfl (etaleOverHom x V'))
  map_id _ := sorry
  map_comp _ _ := sorry

/-- `smallEtaleToTotal x` is objectwise the chosen cartesian pullback of `x`
along the associated `Over S` morphism of an étale neighborhood. -/
theorem smallEtaleToTotal_obj {X : GroupoidsOver S} (x : X.total)
    (V' : SmallStandardTopology.etale.site (X.p.obj x).left) :
    (smallEtaleToTotal x).obj V' =
      pullbackObj (p := X.p) rfl (etaleOverHom x V') :=
  sorry

/-- The underlying scheme of the cartesian lift of `x` along an étale
neighborhood `V'` is the domain of `V'`. -/
def smallEtaleSchemeProjectionApp {X : GroupoidsOver S} (x : X.total)
    (V' : SmallStandardTopology.etale.site (X.p.obj x).left) :
    (smallEtaleToTotal x ⋙ X.p ⋙ Over.forget S).obj V' ⟶
      (SmallStandardTopology.toOver .etale (X.p.obj x).left ⋙
        Over.forget (X.p.obj x).left).obj V' :=
  eqToHom
    (congrArg (fun U : Over S ↦ U.left)
      (pullbackObj_proj (p := X.p) rfl (etaleOverHom x V')))

/-- The scheme-valued comparison from the image of `smallEtaleToTotal x` under
`p` to the underlying scheme of an étale neighborhood of `U = p(x)`. -/
def smallEtaleSchemeProjection {X : GroupoidsOver S} (x : X.total) :
    smallEtaleToTotal x ⋙ X.p ⋙ Over.forget S ⟶
      SmallStandardTopology.toOver .etale (X.p.obj x).left ⋙
        Over.forget (X.p.obj x).left where
  app := smallEtaleSchemeProjectionApp x
  naturality := sorry

/-- The comparison of structure sheaves from `𝒪_{U_étale}` to the restriction of
`𝒪_X` along `smallEtaleToTotal x`. -/
def smallEtaleStructureSheafMap {X : GroupoidsOver S} (x : X.total) :
    smallStructurePresheaf .etale (X.p.obj x).left ⟶
      (smallEtaleToTotal x).op ⋙ (structureSheaf X).obj :=
  let U := (X.p.obj x).left
  Scheme.Site.structurePresheafMap
    (SmallStandardTopology.toOver .etale U ⋙ Over.forget U)
    (X.p ⋙ Over.forget S) (smallEtaleToTotal x) (smallEtaleSchemeProjection x)

/-- On an étale neighborhood `V'` of `U = p(x)`, `smallEtaleStructureSheafMap`
is the map on global sections induced by the scheme projection. -/
theorem smallEtaleStructureSheafMap_app {X : GroupoidsOver S} (x : X.total)
    (V' : SmallStandardTopology.etale.site (X.p.obj x).left) :
    (smallEtaleStructureSheafMap x).app (op V') =
      RingCat.ofHom (smallEtaleSchemeProjectionApp x V').appTop.hom :=
  sorry

/-- Restriction of a presheaf of `𝒪_X`-modules to the small étale site of
`U = p(x)`, as a presheaf of `𝒪_{U_étale}`-modules. -/
def restrictToSmallEtalePresheaf {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (x : X.total) :
    PresheafOfModules.{u} (smallStructurePresheaf .etale (X.p.obj x).left) :=
  (PresheafOfModules.pushforward (smallEtaleStructureSheafMap x)).obj F

/-- Sections of `restrictToSmallEtalePresheaf F x` over an étale neighborhood
`V'` are the sections of `F` on the image of `V'` in `X`, with scalars
restricted along `smallEtaleStructureSheafMap`. -/
theorem restrictToSmallEtalePresheaf_obj {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (x : X.total)
    (V' : SmallStandardTopology.etale.site (X.p.obj x).left) :
    (restrictToSmallEtalePresheaf F x).obj (op V') =
      (ModuleCat.restrictScalars
        ((smallEtaleStructureSheafMap x).app (op V')).hom).obj
        (F.obj (op ((smallEtaleToTotal x).obj V'))) :=
  sorry

/-- If `F` is a sheaf for the étale topology on `X`, then its restriction to the
small étale site of `U = p(x)` is a sheaf. -/
theorem restrictToSmallEtalePresheaf_isSheaf {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (x : X.total)
    (hF : Presheaf.IsSheaf X.etaleTopology F.presheaf) :
    Presheaf.IsSheaf (SmallStandardTopology.etale.topology (X.p.obj x).left)
      (restrictToSmallEtalePresheaf F x).presheaf :=
  sorry

/-- Restriction of a presheaf of `𝒪_X`-modules to the small étale site of
`U = p(x)`, packaged as a sheaf of `𝒪_{U_étale}`-modules. The étale-sheaf
hypothesis is required: an arbitrary module presheaf need not restrict to a
sheaf on `U_étale`. -/
def restrictToSmallEtale {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (x : X.total)
    (hF : Presheaf.IsSheaf X.etaleTopology F.presheaf) :
    SheafOfModules.{u} (smallStructureSheaf .etale (X.p.obj x).left) where
  val := restrictToSmallEtalePresheaf F x
  isSheaf := restrictToSmallEtalePresheaf_isSheaf F x hF

/-- The underlying module presheaf of `restrictToSmallEtale F x hF` is
`restrictToSmallEtalePresheaf F x`. -/
theorem restrictToSmallEtale_val {X : GroupoidsOver S}
    (F : PresheafOfModules.{u} (structureSheaf X).obj) (x : X.total)
    (hF : Presheaf.IsSheaf X.etaleTopology F.presheaf) :
    (restrictToSmallEtale F x hF).val = restrictToSmallEtalePresheaf F x :=
  sorry

end AlgebraicGeometry.GroupoidsOver
