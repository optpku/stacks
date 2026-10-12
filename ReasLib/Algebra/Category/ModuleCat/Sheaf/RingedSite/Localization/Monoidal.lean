/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.ProjectionFormula
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sheafification.Localization
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Over
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Pushforward
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal restriction to a localized ringed site

Restriction of module sheaves to the slice over an object preserves the tensor unit and tensor
products.  On presheaves, its strong-monoidal structure is transported from plain precomposition
along the explicit identity-restriction isomorphism.  The sheaf-level structure is then descended
through module sheafification.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{w}) (U : C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

namespace Construction

/-- The pointwise monoidal structure on module presheaves over the restricted commutative-ring
presheaf.  This bridges the direct precomposition presentation of the underlying ring presheaf. -/
@[stacks 0FRV "slice presheaf monoidal presentation", implicit_reducible]
noncomputable def precompMonoidalCategory :
    MonoidalCategory
      (PresheafOfModules.{w} ((Over.forget U).op ⋙ (ringSheaf J O).obj)) :=
  PresheafOfModules.monoidalCategory (R := (Over.forget U).op ⋙ O.obj)

/-- Plain precomposition to `C / U`, presented over the underlying ring presheaf of `O`, has
Mathlib's canonical strong-monoidal structure. -/
@[stacks 0FRV "strong-monoidal plain presheaf restriction", implicit_reducible]
noncomputable def precompositionMonoidal :
    @Functor.Monoidal
      (PresheafOfModules.{w} (ringSheaf J O).obj) _
      (PresheafOfModules.monoidalCategory (R := O.obj))
      (PresheafOfModules.{w} ((Over.forget U).op ⋙ (ringSheaf J O).obj)) _
      (precompMonoidalCategory O U)
      (PresheafOfModules.pushforward₀
        (Over.forget U) (ringSheaf J O).obj) :=
  inferInstanceAs
    (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget U) O.obj).Monoidal

/-- Restriction of module presheaves to `C / U` is canonically strong monoidal. -/
@[stacks 0FRV "strong-monoidal presheaf restriction", implicit_reducible]
noncomputable def presheafMonoidal :
    @Functor.Monoidal
      (PresheafOfModules.{w} (ringSheaf J O).obj) _
      (PresheafOfModules.monoidalCategory (R := O.obj))
      (PresheafOfModules.{w} ((Over.forget U).op ⋙ (ringSheaf J O).obj)) _
      (precompMonoidalCategory O U)
      (PresheafOfModules.overFunctor (ringSheaf J O).obj U) :=
  @Functor.Monoidal.transport
    (PresheafOfModules.{w} (ringSheaf J O).obj) _
    (PresheafOfModules.monoidalCategory (R := O.obj))
    (PresheafOfModules.{w} ((Over.forget U).op ⋙ (ringSheaf J O).obj)) _
    (precompMonoidalCategory O U) _ _ (precompositionMonoidal O U)
    (PresheafOfModules.Restriction.overNatIso (ringSheaf J O).obj U).symm

section Sheafification

variable [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Presheaf restriction followed by module sheafification on `C / U` is canonically strong
monoidal. -/
@[stacks 0FRV "monoidal sheafified presheaf restriction", implicit_reducible]
noncomputable def compositeMonoidal :
    @Functor.Monoidal
      (PresheafOfModules.{w} (ringSheaf J O).obj) _
      (PresheafOfModules.monoidalCategory (R := O.obj))
      (SheafOfModules.{w} ((ringSheaf J O).over U)) _
      (SheafOfModules.RingedSite.moduleMonoidalCategory (O.over U))
      (PresheafOfModules.overFunctor (ringSheaf J O).obj U ⋙
        PresheafOfModules.sheafification
          (R₀ := ((ringSheaf J O).over U).obj)
          (R := (ringSheaf J O).over U)
          (𝟙 ((ringSheaf J O).over U).obj)) :=
  -- The explicit presentation arguments pin the target `ringSheaf` presentation; the
  -- corresponding `O.over U` structure is only isomorphic, not definitionally equal.
  @Functor.Monoidal.instComp
    (PresheafOfModules.{w} (ringSheaf J O).obj) _
    (PresheafOfModules.monoidalCategory (R := O.obj))
    (PresheafOfModules.{w} ((Over.forget U).op ⋙ (ringSheaf J O).obj)) _
    (precompMonoidalCategory O U)
    (SheafOfModules.{w} ((ringSheaf J O).over U)) _
    (SheafOfModules.RingedSite.moduleMonoidalCategory (O.over U))
    (PresheafOfModules.overFunctor (ringSheaf J O).obj U)
    (PresheafOfModules.sheafification
      (R₀ := ((ringSheaf J O).over U).obj)
      (R := (ringSheaf J O).over U)
      (𝟙 ((ringSheaf J O).over U).obj))
    (presheafMonoidal O U)
    (SheafOfModules.RingedSite.Tensor.sheafificationMonoidal (O.over U))

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]

/-- The natural comparison between restricted ambient sheafification and sheafification after
presheaf restriction is the localization lifting that defines sheaf restriction. -/
@[stacks 0FRV "localized restriction lifting", implicit_reducible]
noncomputable def lifting :
    Localization.Lifting
      (PresheafOfModules.sheafification
        (R₀ := (ringSheaf J O).obj)
        (R := ringSheaf J O)
        (𝟙 (ringSheaf J O).obj))
      (SheafOfModules.RingedSite.Tensor.weakEquivalences O)
      (PresheafOfModules.overFunctor (ringSheaf J O).obj U ⋙
        PresheafOfModules.sheafification
          (R₀ := ((ringSheaf J O).over U).obj)
          (R := (ringSheaf J O).over U)
          (𝟙 ((ringSheaf J O).over U).obj))
      (restriction O U) where
  iso := SheafOfModules.Localization.ModuleSheafification.overNatIso
    (ringSheaf J O) U

end Sheafification

end Construction

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]

/-- Restriction of module sheaves to a localized ringed site is canonically strong monoidal. -/
@[stacks 0FRV "strong-monoidal localized restriction", implicit_reducible]
noncomputable def restrictionMonoidal :
    (restriction O U : SheafOfModules.{w} (ringSheaf J O) ⥤
      SheafOfModules.{w} ((ringSheaf J O).over U)).Monoidal :=
  @Localization.Monoidal.functorMonoidalOfComp
    _ _ _ _ _ _ _ _ _
    (PresheafOfModules.sheafification
      (R₀ := (ringSheaf J O).obj)
      (R := ringSheaf J O)
      (𝟙 (ringSheaf J O).obj))
    (SheafOfModules.RingedSite.Tensor.weakEquivalences O)
    _ (SheafOfModules.RingedSite.Tensor.sheafificationMonoidal O)
    (restriction O U)
    (PresheafOfModules.overFunctor (ringSheaf J O).obj U ⋙
      PresheafOfModules.sheafification
        (R₀ := ((ringSheaf J O).over U).obj)
        (R := (ringSheaf J O).over U)
        (𝟙 ((ringSheaf J O).over U).obj))
    (Construction.compositeMonoidal O U) _ (Construction.lifting O U)

end SheafOfModules.RingedSite.Localization

end
