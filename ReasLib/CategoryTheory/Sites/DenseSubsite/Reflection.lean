module

public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import ReasLib.CategoryTheory.Sites.LocallyInjective

/-!
# Reflection along cover-dense functors of sites

A continuous, cover-dense functor reflects local injectivity and local
surjectivity after restriction of sheaves.  The `Type`-valued categorical
consequences are kept here as instances, while the local-predicate forms
remain available for arbitrary concrete coefficients.
-/

@[expose] public section

universe uC uD uA vC vD vA wA w

namespace CategoryTheory

namespace Functor

namespace IsCoverDense

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

section

variable {A : Type uA} [Category.{vA} A]
variable {FA : A → A → Type*} {CA : A → Type wA}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{wA} A FA]

/-- A continuous cover-dense functor reflects local injectivity of sheaf
morphisms, with an explicit cover-density witness. -/
theorem reflectsLocallyInjective_of_isCoverDense
    (F : C ⥤ D) [F.IsContinuous J K] (h_dense : F.IsCoverDense K)
    {X Y : Sheaf K A} (f : X ⟶ Y)
    (h_locally_injective :
      Sheaf.IsLocallyInjective ((F.sheafPushforwardContinuous A J K).map f)) :
    Sheaf.IsLocallyInjective f := sorry

/-- A continuous cover-dense functor reflects local injectivity of sheaf
morphisms through its canonical cover-density instance. -/
theorem reflectsLocallyInjective
    (F : C ⥤ D) [F.IsContinuous J K] [F.IsCoverDense K]
    {X Y : Sheaf K A} (f : X ⟶ Y)
    (h_locally_injective :
      Sheaf.IsLocallyInjective ((F.sheafPushforwardContinuous A J K).map f)) :
    Sheaf.IsLocallyInjective f := sorry

/-- A continuous cover-dense functor reflects local surjectivity of sheaf
morphisms, with an explicit cover-density witness. -/
theorem reflectsLocallySurjective_of_isCoverDense
    (F : C ⥤ D) [F.IsContinuous J K] (h_dense : F.IsCoverDense K)
    {X Y : Sheaf K A} (f : X ⟶ Y)
    (h_locally_surjective :
      Sheaf.IsLocallySurjective ((F.sheafPushforwardContinuous A J K).map f)) :
    Sheaf.IsLocallySurjective f := sorry

/-- A continuous cover-dense functor reflects local surjectivity of sheaf
morphisms through its canonical cover-density instance. -/
theorem reflectsLocallySurjective
    (F : C ⥤ D) [F.IsContinuous J K] [F.IsCoverDense K]
    {X Y : Sheaf K A} (f : X ⟶ Y)
    (h_locally_surjective :
      Sheaf.IsLocallySurjective ((F.sheafPushforwardContinuous A J K).map f)) :
    Sheaf.IsLocallySurjective f := sorry

end

/-- The direct image along a continuous cover-dense functor reflects
monomorphisms of `Type`-valued sheaves, with an explicit cover-density
witness. -/
theorem sheafPushforwardContinuous_reflectsMonomorphisms_of_isCoverDense
    (F : C ⥤ D) [F.IsContinuous J K] (h_dense : F.IsCoverDense K) :
    (F.sheafPushforwardContinuous (Type w) J K).ReflectsMonomorphisms := sorry

/-- The direct image along a continuous cover-dense functor reflects
epimorphisms of `Type`-valued sheaves, with an explicit cover-density
witness. -/
theorem sheafPushforwardContinuous_reflectsEpimorphisms_of_isCoverDense
    (F : C ⥤ D) [F.IsContinuous J K] (h_dense : F.IsCoverDense K)
    [HasSheafify J (Type w)] :
    (F.sheafPushforwardContinuous (Type w) J K).ReflectsEpimorphisms := sorry

/-- The direct image along a continuous cover-dense functor reflects
monomorphisms of `Type`-valued sheaves. -/
instance sheafPushforwardContinuous_reflectsMonomorphisms
    (F : C ⥤ D) [F.IsContinuous J K] [F.IsCoverDense K] :
    (F.sheafPushforwardContinuous (Type w) J K).ReflectsMonomorphisms := sorry

/-- The direct image along a continuous cover-dense functor reflects
epimorphisms of `Type`-valued sheaves when the target sheaf category has
sheafification. -/
instance sheafPushforwardContinuous_reflectsEpimorphisms
    (F : C ⥤ D) [F.IsContinuous J K] [F.IsCoverDense K]
    [HasSheafify J (Type w)] :
    (F.sheafPushforwardContinuous (Type w) J K).ReflectsEpimorphisms := sorry

end IsCoverDense

end Functor

end CategoryTheory
