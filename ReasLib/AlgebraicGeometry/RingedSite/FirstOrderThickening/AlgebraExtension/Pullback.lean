/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRing.Sheaf.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.AlgebraExtension.Presentation
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.ExtMap

/-! # Algebra pullback of square-zero extensions -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf.CommRing
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite CategoryTheory.Sheaf.FreeAlgebra

noncomputable section
set_option backward.privateInPublic true

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening.Solution

-- Local instance justification (defeq pin): the presentation comparison and module localization must use the same standard derived category.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the unbundled module category must select the same localization dictionary as the ringed-site category.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {A B E : Sheaf J CommRingCat.{u}} {f : A ⟶ B} {g : B ⟶ E}
variable {G : SheafOfModules (ringSheaf J E)}
variable (S : Solution (𝟙 A) (isSquareZero_id A) (f ≫ g) G (zeroKernelMap (f ≫ g) G))

namespace Pullback

/-- Pullback of a locally surjective extension remains locally surjective. -/
private theorem proj_isLocallySurjective :
    Sheaf.IsLocallySurjective (Limits.pullback.snd S.proj g) := sorry

/-- The kernel of the fibre-product projection is square zero. -/
private theorem proj_isSquareZero :
    KernelIdeal.IsSquareZero (Limits.pullback.snd S.proj g) := sorry

/-- The fibre-product projection satisfies the first isomorphism theorem. -/
private def quotientIsIso :
    IsIso (KernelIdeal.quotientComparison (Limits.pullback.snd S.proj g)) :=
  @KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _
    (Limits.pullback.snd S.proj g) _ (proj_isLocallySurjective S)

/-- The first projection on kernels as a map of underlying additive sheaves. -/
private def kernelAdditive
    (h : (kernel.ι (KernelIdeal.underlyingProjection (Limits.pullback.snd S.proj g)) ≫
      SheafOfModules.unitUnderlyingMap (ringSheafMap (Limits.pullback.fst S.proj g))) ≫
        KernelIdeal.underlyingProjection S.proj = 0) :
    (SheafOfModules.toSheaf (ringSheaf J B)).obj
        ((proj_isSquareZero S).targetModule (quotientIsIso S)) ⟶
      (SheafOfModules.toSheaf (ringSheaf J E)).obj G :=
  ((proj_isSquareZero S).targetModuleForgetIso (quotientIsIso S)).hom ≫
    (KernelIdeal.underlyingKernelIso (Limits.pullback.snd S.proj g)).hom ≫
    kernel.lift (KernelIdeal.underlyingProjection S.proj)
      (kernel.ι (KernelIdeal.underlyingProjection (Limits.pullback.snd S.proj g)) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap (Limits.pullback.fst S.proj g))) h ≫
    (KernelIdeal.underlyingKernelIso S.proj).inv ≫
    (S.proj_squareZero.targetModuleForgetIso S.proj_quotient_isIso).inv ≫
    (SheafOfModules.toSheaf (ringSheaf J E)).map S.kernelIso.hom

/-- The first projection kills the quotient map on kernels and is linear over the source ring. -/
private theorem kernelMap_laws :
    ((kernel.ι (KernelIdeal.underlyingProjection (Limits.pullback.snd S.proj g)) ≫
      SheafOfModules.unitUnderlyingMap (ringSheafMap (Limits.pullback.fst S.proj g))) ≫
        KernelIdeal.underlyingProjection S.proj = 0) ∧
    (∀ h U (r : B.obj.obj U) x,
      (kernelAdditive S h).hom.app U
          ((((proj_isSquareZero S).targetModule (quotientIsIso S)).val.obj U).isModule.smul r x) =
        (G.val.obj U).isModule.smul (g.hom.app U r) ((kernelAdditive S h).hom.app U x)) := sorry

/-- The first projection identifies the pullback kernel with restricted coefficients. -/
private def kernelMap :
    (proj_isSquareZero S).targetModule (quotientIsIso S) ⟶ (restrictionAlong g).obj G where
  val := PresheafOfModules.homMk
    ((sheafToPresheaf J AddCommGrpCat.{u}).map (kernelAdditive S (kernelMap_laws S).1))
    ((kernelMap_laws S).2 _)

/-- The first-projection map on coefficient kernels is invertible. -/
private theorem kernelMap_isIso : IsIso (kernelMap S) := sorry

/-- The kernel identification induced by the first projection of the fibre product. -/
def kernelIso : (proj_isSquareZero S).targetModule (quotientIsIso S) ≅
    (restrictionAlong g).obj G :=
  @asIso _ _ _ _ (kernelMap S) (kernelMap_isIso S)

/-- The pullback base map commutes with the projection and induces the zero base-kernel map. -/
private theorem pullbackAlong_laws :
    ((Limits.pullback.lift S.structureMap f S.commutes) ≫
        Limits.pullback.snd S.proj g = 𝟙 A ≫ f) ∧
    (∀ h : (Limits.pullback.lift S.structureMap f S.commutes) ≫
        Limits.pullback.snd S.proj g = 𝟙 A ≫ f,
      kernelMapOf (𝟙 A) (isSquareZero_id A) f (Limits.pullback.snd S.proj g)
          (proj_isSquareZero S) (quotientIsIso S)
          (Limits.pullback.lift S.structureMap f S.commutes) h ≫
        (restrictionAlong f).map (kernelIso S).hom =
          zeroKernelMap f ((restrictionAlong g).obj G)) := sorry

end Pullback

/-- Pullback of a square-zero algebra extension along a morphism of quotient algebras. -/
def pullbackAlong : Solution (𝟙 A) (isSquareZero_id A) f
    ((restrictionAlong g).obj G) (zeroKernelMap f ((restrictionAlong g).obj G)) where
  middle := Limits.pullback S.proj g
  proj := Limits.pullback.snd S.proj g
  structureMap := Limits.pullback.lift S.structureMap f S.commutes
  proj_locallySurjective := Pullback.proj_isLocallySurjective S
  proj_squareZero := Pullback.proj_isSquareZero S
  proj_quotient_isIso := Pullback.quotientIsIso S
  commutes := (Pullback.pullbackAlong_laws S).1
  kernelIso := Pullback.kernelIso S
  induces_c := (Pullback.pullbackAlong_laws S).2 _

/-- The middle algebra of pullback is the ring-sheaf fibre product. -/
theorem pullbackAlong_middle : (pullbackAlong S).middle = Limits.pullback S.proj g := sorry

/-- The projection of pullback is the second fibre-product projection. -/
theorem pullbackAlong_proj : (pullbackAlong S).proj = Limits.pullback.snd S.proj g := sorry

/-- The algebra structure of pullback is the canonical fibre-product lift. -/
theorem pullbackAlong_structureMap :
    (pullbackAlong S).structureMap = Limits.pullback.lift S.structureMap f S.commutes := sorry

/-- The first projection respects quotient and base maps and is the identity on identified kernels. -/
theorem pullbackAlong_spec :
    Limits.pullback.fst S.proj g ≫ S.proj = (pullbackAlong S).proj ≫ g ∧
    (pullbackAlong S).structureMap ≫ Limits.pullback.fst S.proj g = S.structureMap ∧
    (∀ U (x : G.val.obj U),
      (Limits.pullback.fst S.proj g).hom.app U
          (KernelIdeal.ιApp (pullbackAlong S).proj U
            ((kernelIso_forget (pullbackAlong S)).hom.hom.app U x)) =
        KernelIdeal.ιApp S.proj U ((kernelIso_forget S).hom.hom.app U x)) := sorry

namespace Pullback

/-- The first-projection map on the underlying generator sheaves. -/
private def presentationMap : underlyingSets (pullbackAlong S) ⟶ underlyingSets S :=
  (sheafForget J).map (Limits.pullback.fst S.proj g)

/-- The free-algebra map induced by the first projection on generators. -/
private def presentationMiddle :
    CategoryTheory.Sheaf.FreeAlgebra.underlying A (underlyingSets (pullbackAlong S)) ⟶
      CategoryTheory.Sheaf.FreeAlgebra.underlying A (underlyingSets S) :=
  (CategoryTheory.Sheaf.FreeAlgebra.evaluation
    (Under.mk (CategoryTheory.Sheaf.FreeAlgebra.base A (underlyingSets S)))
    (underlyingSets (pullbackAlong S))
    (presentationMap S ≫ CategoryTheory.Sheaf.FreeAlgebra.generator A (underlyingSets S))).right

/-- The induced free-algebra map respects the base and evaluation maps. -/
private theorem presentationHom_laws :
    CommSq (𝟙 A)
      (CategoryTheory.Sheaf.FreeAlgebra.base A (underlyingSets (pullbackAlong S)))
      (CategoryTheory.Sheaf.FreeAlgebra.base A (underlyingSets S)) (presentationMiddle S) ∧
    CommSq (presentationMiddle S)
      (eval (underlyingSets (pullbackAlong S))
        (assignOf (pullbackAlong S) (underlyingSets (pullbackAlong S))
          (underlyingAssign' (pullbackAlong S))))
      (eval (underlyingSets S) (assignOf S (underlyingSets S) (underlyingAssign' S))) g := sorry

/-- The morphism between the polynomial presentations of an extension and its pullback. -/
private def presentationHom : Presentation.Hom
    (CategoryTheory.Sheaf.FreeAlgebra.base A (underlyingSets (pullbackAlong S)))
    (eval (underlyingSets (pullbackAlong S))
      (assignOf (pullbackAlong S) (underlyingSets (pullbackAlong S))
        (underlyingAssign' (pullbackAlong S))))
    (CategoryTheory.Sheaf.FreeAlgebra.base A (underlyingSets S))
    (eval (underlyingSets S) (assignOf S (underlyingSets S) (underlyingAssign' S))) where
  base := 𝟙 A
  middle := presentationMiddle S
  target := g
  baseSq := (presentationHom_laws S).1
  targetSq := (presentationHom_laws S).2

/-- The induced morphism of presentation cotangent complexes. -/
private def cotangentMap :
    (extendComplex g).obj
      (Presentation.ofGenerators (underlyingSets (pullbackAlong S))
        (assignOf (pullbackAlong S) (underlyingSets (pullbackAlong S))
          (underlyingAssign' (pullbackAlong S)))) ⟶
    Presentation.ofGenerators (underlyingSets S)
      (assignOf S (underlyingSets S) (underlyingAssign' S)) :=
  Presentation.Hom.map (presentationHom S)

/-- The conormal map is the degree-minus-one component of the presentation comparison. -/
private def conormalMap :
    (extendAlong g).obj
      ((Presentation.ofGenerators (underlyingSets (pullbackAlong S))
        (assignOf (pullbackAlong S) (underlyingSets (pullbackAlong S))
          (underlyingAssign' (pullbackAlong S)))).X (-1)) ⟶
    (Presentation.ofGenerators (underlyingSets S)
      (assignOf S (underlyingSets S) (underlyingAssign' S))).X (-1) :=
  (cotangentMap S).f (-1)
/-- The conormal class of a pulled-back extension is the original conormal class
precomposed with the induced degree `-1` presentation map. -/
theorem conormalMap_comp
    :
    conormalHom (pullbackAlong S) (underlyingSets (pullbackAlong S))
        (underlyingAssign' (pullbackAlong S))
        (assignOf (pullbackAlong S) (underlyingSets (pullbackAlong S))
          (underlyingAssign' (pullbackAlong S))) rfl =
      (extendRestrictAdj g).homEquiv
          ((Presentation.ofGenerators (underlyingSets (pullbackAlong S))
              (assignOf (pullbackAlong S) (underlyingSets (pullbackAlong S))
                (underlyingAssign' (pullbackAlong S)))).X (-1))
          ((Presentation.ofGenerators (underlyingSets S)
              (assignOf S (underlyingSets S) (underlyingAssign' S))).X (-1))
          (conormalMap S) ≫
        (restrictionAlong g).map
          (conormalHom S (underlyingSets S) (underlyingAssign' S)
            (assignOf S (underlyingSets S) (underlyingAssign' S)) rfl) :=
  sorry

/-- The induced presentation map represents the canonical cotangent comparison
after derived scalar extension and the derived presentation comparisons. -/
theorem cotangentMap_comparison
    :
    (SameSite.pullbackDerived g).map
        (Presentation.derivedComparison
            (underlyingSets (pullbackAlong S))
            (assignOf (pullbackAlong S) (underlyingSets (pullbackAlong S))
              (underlyingAssign' (pullbackAlong S)))) ≫
      naiveCotangentComparison f g =
      (Functor.LeftDerived.Homotopy.cochainCounit
            ((sameSiteHom g).modulePullback)).app
          (Presentation.ofGenerators (underlyingSets (pullbackAlong S))
            (assignOf (pullbackAlong S) (underlyingSets (pullbackAlong S))
              (underlyingAssign' (pullbackAlong S)))) ≫
        DerivedCategory.Q.map
          ((pullbackComplexExtendIso g).hom.app
              (Presentation.ofGenerators (underlyingSets (pullbackAlong S))
                (assignOf (pullbackAlong S) (underlyingSets (pullbackAlong S))
                  (underlyingAssign' (pullbackAlong S)))) ≫
            cotangentMap S) ≫
          (Presentation.derivedComparison (underlyingSets S)
              (assignOf S (underlyingSets S) (underlyingAssign' S))) :=
  sorry

end Pullback

end SheafOfModules.RingedSite.FirstOrderThickening.Solution
