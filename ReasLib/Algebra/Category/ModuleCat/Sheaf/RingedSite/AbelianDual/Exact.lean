module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.CategoryTheory.Abelian.Injective.Characterizations
public import ReasLib.CategoryTheory.Monoidal.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness and injectivity for abelian duals

Dualization into an injective abelian sheaf is exact. Consequently, the dual of a flat module
sheaf is injective, and dualizing after a functorial flat replacement gives an injective-valued
endofunctor. Exactness and bidual composition allow the ring-valued sheaf to live in an
independent universe. The flatness statements use the canonical tensor structure, whose current
Mathlib interface places rings and modules in the same universe.

These results concern the abelian-sheaf-valued dual from `AbelianDual.Functor`, not an arbitrary
internal Hom in a closed monoidal category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.AbelianDual

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section General

variable [J.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{max u v z}]
variable (O : Sheaf J CommRingCat.{w})
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v z}]

/-- Dualization into an injective abelian sheaf is exact. -/
@[stacks 01DR]
theorem exact
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z}) [Injective 𝒥] :
    exactFunctor
      (ringedSiteModuleCategory.{u, v, max u v z, w} J O)ᵒᵖ
      (ringedSiteModuleCategory.{u, v, max u v z, w} J O)
      (functor O 𝒥) := sorry

/-- Dualize, apply a chosen covariant replacement functor, and dualize again. -/
@[stacks 01DT "flat-bidual functor"]
abbrev flatBidualFunctor
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O ⥤
      ringedSiteModuleCategory.{u, v, max u v z, w} J O) :
    ringedSiteModuleCategory.{u, v, max u v z, w} J O ⥤
      ringedSiteModuleCategory.{u, v, max u v z, w} J O :=
  (functor O 𝒥).rightOp ⋙ F.op ⋙ functor O 𝒥

/-- The value of the abelian-sheaf-valued flat-bidual functor at a module sheaf. -/
abbrev flatBidual
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O ⥤
      ringedSiteModuleCategory.{u, v, max u v z, w} J O)
    (G : ringedSiteModuleCategory.{u, v, max u v z, w} J O) :
    ringedSiteModuleCategory.{u, v, max u v z, w} J O :=
  (flatBidualFunctor O 𝒥 F).obj G

end General

section CanonicalTensor

variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v z} RingCat.{max u v z})]
variable [HasSheafify J AddCommGrpCat.{max u v z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v z}]
variable (O : Sheaf J CommRingCat.{max u v z})

/-- The abelian dual of a flat module sheaf into an injective abelian sheaf is injective as an
`O`-module sheaf. -/
@[stacks 01DT "flat-object form"]
theorem injective_dual
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z}) [Injective 𝒥]
    (P : ringedSiteModuleCategory.{u, v, max u v z, max u v z} J O)
    [MonoidalCategory.IsFlat P] :
    Injective (dual O 𝒥 P) := sorry

/-- If `F` functorially chooses flat module sheaves, every value of the corresponding
abelian-sheaf-valued flat-bidual functor is injective. -/
@[stacks 01DT]
theorem injective_flatBidual
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z}) [Injective 𝒥]
    (F : ringedSiteModuleCategory.{u, v, max u v z, max u v z} J O ⥤
      ringedSiteModuleCategory.{u, v, max u v z, max u v z} J O)
    [∀ X, MonoidalCategory.IsFlat (F.obj X)]
    (G : ringedSiteModuleCategory.{u, v, max u v z, max u v z} J O) :
    Injective (flatBidual O 𝒥 F G) := sorry

end CanonicalTensor

end SheafOfModules.RingedSite.AbelianDual
