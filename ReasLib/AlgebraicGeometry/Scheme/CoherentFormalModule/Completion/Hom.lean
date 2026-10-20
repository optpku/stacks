module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.InternalHom

/-!
# Morphisms between completions of coherent modules

The ideal-power quotients of an internal-Hom sheaf form a canonical inverse system of global
sections. Evaluation at every quotient stage gives a comparison from its inverse limit to
morphisms between the corresponding completed coherent modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace CoherentCompletionFunctor

/-- The inverse system whose stage `n` consists of global sections of
`Hom(G, F) / I ^ n Hom(G, F)`. -/
noncomputable def homSectionsSystem
    {X : Scheme.{u}} (I : X.IdealSheafData)
    (F G : RingedSpace.Coh X.toRingedSpace) : ℕᵒᵖ ⥤ Type u :=
  SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.sectionsSystem.{u, u, u}
    I.toSubobject
      (SheafOfModules.RingedSite.InternalHom.obj X.toRingedSpace.sheaf G.obj F.obj)

/-- The section represented by a compatible family in the inverse limit at stage `n`. -/
noncomputable def homSection
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F G : RingedSpace.Coh X.toRingedSpace)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
      I.toSubobject
        (SheafOfModules.RingedSite.InternalHom.obj X.toRingedSpace.sheaf G.obj F.obj) n).sections :=
  limit.π (homSectionsSystem I F G) (op n) x

/-- Evaluation of a compatible internal-Hom section on the stage-`n` ideal-power quotients. -/
noncomputable def homQuotientMap
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F G : RingedSpace.Coh X.toRingedSpace)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
        I.toSubobject G.obj n ⟶
      SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
        I.toSubobject F.obj n :=
  SheafOfModules.RingedSite.InternalHom.sectionsHomEquiv X.toRingedSpace.sheaf
    (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
      I.toSubobject G.obj n)
    (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
      I.toSubobject F.obj n)
    (SheafOfModules.sectionsMap
      (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.InternalHom.comparison
        I.toSubobject G.obj F.obj n)
      (homSection F G x n))

/-- The map on stage `n` obtained by transporting evaluation through a completion presentation. -/
noncomputable def homComparisonStageMap
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (F G : RingedSpace.Coh X.toRingedSpace)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    (((ctx.obj G).obj).obj (op n)) ⟶ (((ctx.obj F).obj).obj (op n)) :=
  ObjectProperty.homMk
    ((ctx.stagePowerQuotientIso G n).inv ≫ homQuotientMap F G x n ≫
      (ctx.stagePowerQuotientIso F n).hom)

/-- The stage maps defined by a compatible family commute with completion transitions. -/
theorem homComparisonStageMap_naturality
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (F G : RingedSpace.Coh X.toRingedSpace)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    ((ctx.obj G).obj).stepMap n ≫ homComparisonStageMap ctx F G x n =
      homComparisonStageMap ctx F G x (n + 1) ≫ ((ctx.obj F).obj).stepMap n := sorry

/-- A compatible family of internal-Hom quotient sections determines a morphism between the
corresponding presented coherent completions. -/
noncomputable def homComparison
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (F G : RingedSpace.Coh X.toRingedSpace) :
    limit (homSectionsSystem I F G) → (ctx.obj G ⟶ ctx.obj F) := fun x ↦
  ObjectProperty.homMk
    (NatTrans.ofOpSequence (homComparisonStageMap ctx F G x)
      (homComparisonStageMap_naturality ctx F G x))

/-- The canonical comparison from the inverse limit of internal-Hom quotient sections to
morphisms between coherent completions is bijective on a Noetherian scheme. -/
theorem homComparison_bijective
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (F G : RingedSpace.Coh X.toRingedSpace) :
    Function.Bijective (homComparison ctx F G) := sorry

end CoherentCompletionFunctor

namespace AlgebraicGeometry.Scheme.CoherentCompletion

/-- The canonical comparison from the inverse limit of the internal-Hom quotient sections to
morphisms between the canonical coherent completions. The presentation-level construction in
`CoherentCompletionFunctor.homComparison` remains available when a noncanonical presentation is
part of the input data. -/
@[stacks 0882 "canonical Hom comparison for coherent completion"]
noncomputable def homComparison
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (F G : RingedSpace.Coh X.toRingedSpace) :
    limit (CoherentCompletionFunctor.homSectionsSystem I F G) →
      ((functor I).obj G ⟶ (functor I).obj F) :=
  CoherentCompletionFunctor.homComparison
    (CoherentCompletionFunctor.canonical X I) F G

/-- The canonical Hom comparison for coherent completion is bijective on a Noetherian scheme. -/
@[stacks 0882 "bijectivity of the canonical Hom comparison"]
theorem homComparison_bijective
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (F G : RingedSpace.Coh X.toRingedSpace) :
    Function.Bijective (homComparison (I := I) F G) := sorry

end AlgebraicGeometry.Scheme.CoherentCompletion
