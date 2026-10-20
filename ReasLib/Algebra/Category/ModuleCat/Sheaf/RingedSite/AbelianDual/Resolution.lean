module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.InjectiveTarget
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FreeFlatCover.Flat
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# The flat-bidual injective resolution

Fix an injective abelian sheaf `𝒥` which separates maps of module sheaves. Applying the canonical
free flat cover to the abelian dual of `M` and dualizing again gives
`J(M) = (FreeFlatCover(Mᵛ))ᵛ`.  Evaluation followed by the dual of the cover epimorphism is a
natural monomorphism `M ⟶ J(M)`, and every `J(M)` is injective.

The site may be locally small in independent object and morphism universes. The construction is
performed in the common universe `max u v w`; existence of extension from each slice is retained
as the exact categorical hypothesis needed by the canonical free flat cover.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.AbelianDual.Resolution

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
variable (O : Sheaf J CommRingCat.{max u v w})
variable [SheafOfModules.Localization.HasLowerShriek.{max u v w} (ringSheaf J O)]
variable (𝒥 : Sheaf J AddCommGrpCat.{max u v w})

/-- The endofunctor `M ↦ (FreeFlatCover(Mᵛ))ᵛ`. -/
@[stacks 01DT "canonical flat-bidual functor"]
abbrev functor :
    ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O ⥤
      ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O :=
  AbelianDual.flatBidualFunctor O 𝒥 (FreeFlatCover.functor O)

/-- The canonical flat-bidual injective object associated to `M`. -/
@[stacks 01DT "canonical flat-bidual object"]
abbrev obj
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O :=
  (functor O 𝒥).obj M

/-- Evaluation into the bidual, followed by dualization of the canonical free flat cover. -/
@[stacks 01DT "canonical map to the flat bidual"]
noncomputable def ιApp
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    M ⟶ obj O 𝒥 M :=
  AbelianDual.toBidual O 𝒥 M ≫
    AbelianDual.map O 𝒥
      (FreeFlatCover.πApp (AbelianDual.dual O 𝒥 M))

/-- The canonical maps to flat biduals are natural in the module sheaf. -/
theorem ι_naturality
    {M N : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O}
    (f : M ⟶ N) :
    (𝟭 (ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O)).map f ≫
        ιApp O 𝒥 N =
      ιApp O 𝒥 M ≫ (functor O 𝒥).map f := sorry

/-- The canonical maps to flat biduals form a natural transformation. -/
@[stacks 01DT "functorial flat-bidual embedding"]
noncomputable def ι :
    𝟭 (ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) ⟶
      functor O 𝒥 where
  app := ιApp O 𝒥
  naturality := fun {_ _} f ↦ ι_naturality O 𝒥 f

/-- Every component of the canonical flat-bidual embedding is monic. -/
@[stacks 01DT "flat-bidual embedding is monic"]
theorem mono_ιApp (h𝒥 : AbelianDual.Separates O 𝒥)
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    Mono (ιApp O 𝒥 M) := sorry

/-- If `𝒥` separates module maps, the natural flat-bidual embedding is monomorphic. -/
@[stacks 01DT "functorial flat-bidual embedding is monic"]
theorem mono_ι (h𝒥 : AbelianDual.Separates O 𝒥) : Mono (ι O 𝒥) := sorry

variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v w} AddCommGrpCat.{max u v w})]
variable [Injective 𝒥]

/-- Every canonical flat-bidual object is injective. -/
@[stacks 01DT "canonical flat bidual is injective", instance]
theorem obj_injective
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    Injective (obj O 𝒥 M) := sorry

/-- The canonical flat-bidual object and embedding give an injective presentation of `M`. -/
@[stacks 01DT "canonical injective presentation"]
noncomputable def presentation (h𝒥 : AbelianDual.Separates O 𝒥)
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    InjectivePresentation M where
  J := obj O 𝒥 M
  injective := obj_injective O 𝒥 M
  f := ιApp O 𝒥 M
  mono := mono_ιApp O 𝒥 h𝒥 M

/-- The flat-bidual construction supplies functorial injective embeddings. -/
@[stacks 01DU "flat-bidual functorial injective embeddings", reducible]
noncomputable def functorialInjectives
    (h𝒥 : AbelianDual.Separates O 𝒥) :
    HasFunctorialInjectives
      (ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) where
  functor := functor O 𝒥
  ι := ι O 𝒥
  mono_app := mono_ιApp O 𝒥 h𝒥
  injective_obj := obj_injective O 𝒥

/-- An injective duality target supplies the flat-bidual functorial injective embeddings. -/
@[stacks 01DU "flat-bidual embeddings from a duality target", reducible]
noncomputable def ofTarget {O : Sheaf J CommRingCat.{max u v w}}
    [SheafOfModules.Localization.HasLowerShriek.{max u v w} (ringSheaf J O)]
    (𝒥 : AbelianDual.InjectiveTarget O) :
    HasFunctorialInjectives
      (ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :=
  functorialInjectives O 𝒥.obj 𝒥.separates

end SheafOfModules.RingedSite.AbelianDual.Resolution
