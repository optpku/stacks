/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial free covers on a ringed site

For a module sheaf `M`, take one copy of the localized structure module `j_{U!} O_U` for
every pair `(U, s)` with `s : M(U)`. Their coproduct maps canonically onto `M`. This leaf owns
the cover data and functoriality; flatness is proved in `FreeFlatCover.Flat`.

The construction uses the common universe `max u v w` containing the site's objects and
morphisms and a chosen ambient universe `w`. This is the least universe at which Mathlib's
current localized structure module is available while still allowing arbitrary locally small
sites. `SheafOfModules.Localization.HasLowerShriek` isolates the exact slice-adjunction
hypothesis; it is inferred automatically on same-universe small sites. The abstract abelian-dual
API keeps the raw ring universe independent where no localized structure module is involved.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FreeFlatCover

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
variable {O : Sheaf J CommRingCat.{max u v w}}
variable [SheafOfModules.Localization.HasLowerShriek.{max u v w} (ringSheaf J O)]

/-- Pairs `(U, s)` consisting of an object of the site and a section of `M` over it. -/
@[stacks 01DQ "free flat cover indices"]
def Index (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :=
  Σ U : C, M.val.obj (op U)

/-- The localized structure module indexed by a section of `M`. -/
noncomputable abbrev summand
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O)
    (i : Index M) :
    ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O :=
  SheafOfModules.Localization.structureModule (ringSheaf J O) i.1

/-- The coproduct of localized structure modules indexed by all local sections of `M`. -/
@[stacks 01DQ "canonical free flat object"]
noncomputable def obj
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O :=
  ∐ fun i : Index M ↦ summand M i

/-- The map from the summand indexed by `(U, s)` which sends its universal section to `s`. -/
@[stacks 01DQ "summand evaluation"]
noncomputable def summandHom
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O)
    (i : Index M) :
    summand M i ⟶ M :=
  (SheafOfModules.Localization.structureModuleHomEquiv
    (ringSheaf J O) i.1 M).symm i.2

/-- The canonical map from the free flat object onto `M`. -/
@[stacks 01DQ "free flat cover"]
noncomputable def πApp
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) : obj M ⟶ M :=
  Sigma.desc (summandHom M)

/-- The canonical free flat cover is an epimorphism. -/
@[stacks 01DQ "free flat cover is epic", instance]
theorem epi_πApp
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    Epi (πApp M) := sorry

namespace Index

/-- A module-sheaf morphism sends the index `(U, s)` to `(U, f(s))`. -/
def map {M N : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O}
    (f : M ⟶ N) :
    Index M → Index N :=
  fun i ↦ ⟨i.1, (f.val.app (op i.1)).hom i.2⟩

/-- The index map associated to an identity morphism is the identity. -/
theorem map_id
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    map (𝟙 M) = id := sorry

/-- Index maps respect composition. -/
theorem map_comp
    {M N P : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O}
    (f : M ⟶ N) (g : N ⟶ P) :
    map (f ≫ g) = map g ∘ map f := sorry

end Index

/-- The morphism between free flat objects induced by a module-sheaf morphism. -/
@[stacks 01DQ "functoriality of the free flat object"]
noncomputable def map
    {M N : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O}
    (f : M ⟶ N) : obj M ⟶ obj N :=
  Sigma.map' (f := summand M) (g := summand N)
    (Index.map f) (fun i ↦ 𝟙 (summand M i))

/-- The free-flat-object map preserves identities. -/
theorem map_id
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    map (𝟙 M) = 𝟙 (obj M) := sorry

/-- The free-flat-object map preserves composition. -/
theorem map_comp
    {M N P : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O}
    (f : M ⟶ N) (g : N ⟶ P) :
    map (f ≫ g) = map f ≫ map g := sorry

/-- The functor assigning the canonical free flat object to a module sheaf. -/
@[stacks 01DQ "functorial free flat object"]
noncomputable def functor
    (O : Sheaf J CommRingCat.{max u v w})
    [SheafOfModules.Localization.HasLowerShriek.{max u v w} (ringSheaf J O)] :
    ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O ⥤
      ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O where
  obj := obj
  map := map
  map_id := map_id
  map_comp := map_comp

/-- Evaluation of the functorial free flat object on an object. -/
@[simp]
theorem functor_obj
    (O : Sheaf J CommRingCat.{max u v w})
    [SheafOfModules.Localization.HasLowerShriek.{max u v w} (ringSheaf J O)]
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    (functor O).obj M = obj M := sorry

/-- Evaluation of the functorial free flat object on a morphism. -/
@[simp]
theorem functor_map
    (O : Sheaf J CommRingCat.{max u v w})
    [SheafOfModules.Localization.HasLowerShriek.{max u v w} (ringSheaf J O)]
    {M N : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O}
    (f : M ⟶ N) :
    (functor O).map f = map f := sorry

/-- The free flat cover commutes with module-sheaf morphisms. -/
theorem π_naturality
    {M N : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O}
    (f : M ⟶ N) :
    (functor O).map f ≫ πApp N =
      πApp M ≫
        (𝟭 (ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O)).map f := sorry

/-- The canonical free flat covers form a natural transformation to the identity. -/
@[stacks 01DQ "functorial free flat cover"]
noncomputable def π
    (O : Sheaf J CommRingCat.{max u v w})
    [SheafOfModules.Localization.HasLowerShriek.{max u v w} (ringSheaf J O)] :
    functor O ⟶
      𝟭 (ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) where
  app := πApp
  naturality := fun {_ _} f ↦ π_naturality f

/-- A component of the functorial free flat cover is the canonical evaluation map. -/
@[simp]
theorem π_app
    (O : Sheaf J CommRingCat.{max u v w})
    [SheafOfModules.Localization.HasLowerShriek.{max u v w} (ringSheaf J O)]
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    (π O).app M = πApp M := sorry

/-- The natural free flat cover is an epimorphism in the endofunctor category. -/
@[stacks 01DQ "functorial free flat cover is epic", instance]
theorem epi_π
    (O : Sheaf J CommRingCat.{max u v w})
    [SheafOfModules.Localization.HasLowerShriek.{max u v w} (ringSheaf J O)] :
    Epi (π O) := sorry

end SheafOfModules.RingedSite.FreeFlatCover
