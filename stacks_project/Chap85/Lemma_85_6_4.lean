module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import stacks_project.Chap85.Lemma_85_6_3

/-!
# Lemma 85.6.4

In Situation 85.3.3, if `O` is a sheaf of rings on `C_total` such that the maps
`f_φ⁻¹ O_n ⟶ O_m` are flat for all `φ : n ⟶ m`, and `I` is injective in `Mod(O)`,
then the degree-`n` restriction `I_n` is injective in `Mod(O_n)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]

/-- Lemma 85.6.4 (1): in Situation 85.3.3 case A, if `O` is a sheaf of rings on
`C_total` such that the maps `f_φ⁻¹ O_n ⟶ O_m` are flat for all `φ : n ⟶ m`, then
`g_n^* : Mod(O) ⥤ Mod(O_n)` preserves injective objects. -/
@[stacks 0D75]
theorem modulePullback_preservesInjectiveObjects (n : SimplexCategory)
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J O φ)) :
    ((stageMorphism C J O n).modulePullback).PreservesInjectiveObjects :=
  sorry

/-- The degree-`n` restriction of an injective sheaf of modules on `C_total` is injective
in `Mod(O_n)` when the maps `f_φ⁻¹ O_n ⟶ O_m` are flat. -/
theorem injective_modulePullback (n : SimplexCategory)
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J O φ))
    (I : SheafOfModules.{w} O) [Injective I] :
    Injective ((stageMorphism C J O n).modulePullback.obj I) :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]

/-- Lemma 85.6.4 (2): in Situation 85.3.3 case B, if `O` is a sheaf of rings on
`C_total` such that the maps `f_φ⁻¹ O_n ⟶ O_m` are flat for all `φ : n ⟶ m`, then
`g_n^* : Mod(O) ⥤ Mod(O_n)` preserves injective objects. -/
@[stacks 0D75]
theorem fiberModulePullback_preservesInjectiveObjects (n : SimplexCategory)
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (fiberRingedToposMap F J O φ)) :
    ((fiberStageMorphism F J O n).modulePullback).PreservesInjectiveObjects :=
  sorry

/-- In case B, the degree-`n` restriction of an injective sheaf of modules on `C_total`
is injective in `Mod(O_n)` when the maps `f_φ⁻¹ O_n ⟶ O_m` are flat. -/
theorem injective_fiberModulePullback (n : SimplexCategory)
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (fiberRingedToposMap F J O φ))
    (I : SheafOfModules.{w} O) [Injective I] :
    Injective ((fiberStageMorphism F J O n).modulePullback.obj I) :=
  sorry

end CategoryTheory.Grothendieck
